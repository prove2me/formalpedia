-- Prove2me | Theorems.Thm_PathCount2k_Supplement_theorem_1_3
-- name    : PathCount2k.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:23:05.5003+00:00
-- url     : https://prove2.me/theorems/e4968d81-7ace-4bb7-a315-8520cd4dbd64
-- title:
--   Theorem 1.3 — $M_k(f)$ of a monotone circuit estimated to $1\pm\varepsilon$ in $2^{\omega k/2}s^4k^{O(1)}\varepsilon^{-2}\log(2/\delta)$ operations
-- statement:
--   Let $\mathcal C$ be a normalized monotone arithmetic circuit (Definition 4.1) of size $s$ (gates plus wires) and output syntactic degree $k$, computing a polynomial $f$, and let $M_k(f)$ be the sum of the coefficients of the degree-$k$ multilinear monomials of $f$. Let $\omega\ge 2$ be any exponent for which square real matrices of order $r$ can be multiplied in $O(r^\omega)$ arithmetic operations. For $0<\varepsilon,\delta<1$, the algorithm of §4 returns $\widehat M$ with
--
--   $$
--   \Pr\big[|\widehat M-M_k(f)|\le\varepsilon M_k(f)\big]\ge1-\delta,
--   $$
--
--   using
--
--   $$
--   2^{\omega k/2}\,s^4\,k^{O(1)}\,\varepsilon^{-2}\log(2/\delta)
--   $$
--
--   arithmetic operations, where the exponent in $k^{O(1)}$ is an absolute constant and the leading constant depends only on $\omega$ and on the constant of the matrix-multiplication routine.
--
--   With the current bound $\omega<2.371339$ this is below $2.275^k s^4 k^{O(1)}\varepsilon^{-2}\log(2/\delta)$. Counting embeddings of paths, trees and other patterns reduces to this problem, and the result improves the earlier $O((3.841^k+s^{o(1)})s\varepsilon^{-6}\log(2/\delta))$ bound of Lokshtanov, Saurabh and Zehavi.
--
--   **Formalization Note** The algorithm is the paper's §4.8 algorithm, written out as the charged program `countMono mmCost` in the cost monad `CapacitatedAssort.General.Work` (weighted arithmetic model). The matrix multiplication enters as its cost function `mmCost` with the hypothesis $\mathrm{mmCost}(r,A,B)\le C_{\mathrm{mm}}r^\omega$ for all $r\ge1$; the probability is the fraction of the tapes of the program's bit budget on which the output is within relative error $\varepsilon$, and the operation bound holds on every tape.
--
--   Differences from the source:
--   - reading: "there is a randomized algorithm … uses … arithmetic operations" → the paper's §4.8 algorithm as the program countMono in the cost monad Work (weighted arithmetic model: every operation, comparison, square root of a weight, loop step, sampling attempt and bit read charged; linear-time median over ℝ); reason: without the program the existence claim is trivial; this is the paper's accounting (Lemma 4.7, §4.8)
--   - reading: "ω < 2.371339 [ADW+25] is any exponent for which square matrices of order r can be multiplied in O(r^ω) arithmetic operations" → for every real ω ≥ 2 and every cost function mmCost of an exact r × r real matrix product with mmCost r A B ≤ C_mm r^ω for all r ≥ 1, there is C (depending on ω, C_mm); the bound 2.371339 is not a hypothesis; reason: "any exponent" quantifies over all valid ω; every genuine routine has ω ≥ 2 (it writes r² entries), while in a charged model a free routine would satisfy O(r^ω) for every ω, so ω ≥ 2 must be stated
--   - reading: "Clifford-algebra multiplication gives T∧(k) = 2^{ωk/2}k^{O(1)}; see [Wło19, BDH18]" → an explicit faithful real matrix representation of the Clifford algebra of order 2^{⌈k/2⌉} with butterfly transforms (2^k k^{O(1)} work) and degree splitting, inside the program; reason: the paper cites this routine and describes it in these terms (p.32); it must be part of the program for the operation count to be meaningful
--   - reading: k^{O(1)} → a universal exponent c quantified before ω, mmCost and the circuit; reason: the meaning of k^{O(1)}
--   - encoding: a monotone circuit (Definition 4.1), its size s, positions 1, …, k, fair random bits → gates numbered topologically with sum gates as lists of (input, weight) pairs (parallel wires repeated) and ordered binary products, s = sizeS = gates + wires, f as an MvPolynomial (Fin n) ℝ, 0-based positions, a uniform tape Fin L → Bool with L = circBits C ε δ, natural log; reason: same instances (every DAG has a topological numbering)
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Theorem 1.3, p.2 (PDF p.3), footnotes 2–3; proof §4, pp.27–34

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Supplement_Circuit
import Definitions.Def_PathCount2k_Supplement_CircuitAlgorithm

open scoped Classical

namespace PathCount2k.Supplement

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026),
**Theorem 1.3** (Counting multilinear monomials), p.2: "Let `C` be a monotone circuit of size `s`
and output syntactic degree `k` that computes `f`. For `0 < ε, δ < 1`, there is a randomized
algorithm returning `M̂` such that `Pr[|M̂ − M_k(f)| ≤ εM_k(f)] ≥ 1 − δ`, where `M_k(f)` is the sum
of the coefficients of the degree-`k` multilinear monomials of `f`. The algorithm uses
`2^{ωk/2} s⁴ k^{O(1)} ε⁻² log(2/δ)` arithmetic operations, where `ω < 2.371339` [ADW+25] is any
exponent for which square matrices of order `r` can be multiplied in `O(r^ω)` arithmetic
operations." Footnote 2 (p.2): the monotone circuit is that of Definition 4.1. Proof: §4,
pp.27–34.

The algorithm is the paper's §4.8 algorithm, the charged program `countMono mmCost`, run on a tape
of `circBits C ε δ` fair bits (`8r max{4, ⌈log₂ D⌉} + RqLD` in the main case, §4.8). There is a
universal constant `c` such that for every real `ω ≥ 2` and every matrix-multiplication cost
`mmCost` with `mmCost r A B ≤ C_mm r^ω` for all `r ≥ 1` and all real `r × r` matrices `A, B`, there
is `C` such that for every normalized monotone circuit `C` (Definition 4.1) over any number of
variables, of size `s` and output syntactic degree `k`, computing `f`, and all `0 < ε, δ < 1`:
1. the fraction of tapes on which `|M̂ − M_k(f)| ≤ ε M_k(f)` is at least `1 − δ`;
2. on every tape the number of charged operations is at most
   `C · 2^{ωk/2} · s⁴ · k^c · ε⁻² · log(2/δ)`.

**Formalization Note.** "There is a randomized algorithm … uses … arithmetic operations" is read as
a statement about the paper's own algorithm, the program `countMono` in the cost monad
`CapacitatedAssort.General.Work` (weighted arithmetic model: square roots of weights are charged
operations). The matrix multiplication enters as its cost function `mmCost` (the product returned
is the exact product), and "multiplied in `O(r^ω)` arithmetic operations" is the hypothesis on
`mmCost`; `C` may depend on `ω` and `C_mm`, the exponent `c` is universal. `ω ≥ 2` holds for every
genuine routine (it writes `r²` entries); in the charged model it must be assumed, since a free
`mmCost` satisfies `O(r^ω)` for every `ω`. `log` is natural. -/
theorem theorem_1_3 :
    ∃ c : ℕ, ∀ ω : ℝ, 2 ≤ ω →
      ∀ (mmCost : (r : ℕ) → Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ → ℕ) (Cmm : ℝ),
        (∀ r : ℕ, 1 ≤ r → ∀ A B : Matrix (Fin r) (Fin r) ℝ,
          (mmCost r A B : ℝ) ≤ Cmm * (r : ℝ) ^ ω) →
        ∃ C : ℝ, ∀ (n : ℕ) (Cc : Circuit n), Cc.Normalized → ∀ ε δ : ℝ,
          0 < ε → ε < 1 → 0 < δ → δ < 1 →
          (((Finset.univ.filter fun b : Fin (circBits Cc ε δ) → Bool =>
              |((countMono mmCost Cc ε δ b).run 0).1 - Mk Cc.poly (Cc.deg Cc.out)| ≤
                ε * Mk Cc.poly (Cc.deg Cc.out)).card : ℝ) / 2 ^ circBits Cc ε δ ≥ 1 - δ) ∧
          ∀ b : Fin (circBits Cc ε δ) → Bool,
            ((((countMono mmCost Cc ε δ b).run 0).2 : ℕ) : ℝ) ≤
              C * (2 : ℝ) ^ (ω * (Cc.deg Cc.out : ℝ) / 2) * (Cc.sizeS : ℝ) ^ 4 *
                (Cc.deg Cc.out : ℝ) ^ c * ε ^ (-2 : ℤ) * Real.log (2 / δ) := by sorry

end PathCount2k.Supplement
