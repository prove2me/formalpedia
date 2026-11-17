-- Prove2me | Theorems.Thm_SuperlatSVP_Supplement_theorem_4_9
-- name    : SuperlatSVP.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:37:55.335719+00:00
-- url     : https://prove2.me/theorems/cce42f98-9b55-473e-9164-7416f363d857
-- title:
--   Theorem 4.9 — quadratic-search SVP in time $2^{(\beta+\frac12\log_2\frac43)n+o(n)}$ and space $(4/3)^{n/2+o(n)}$ under (2.3); $(8e/(3\pi))^{n/2+o(n)}$ time on every lattice
-- statement:
--   **Theorem 4.9 (quadratic-search SVP).** Write $\mathrm{inputs}(n)$ for the invertible bases $B\in\mathbb Q^{n\times n}$, and $\ell$ for the bit length of the input word $(n,B)$.
--
--   1. **Under the point-count bound.** Let $\beta\ge\tfrac12\log_2(4/3)$, and let $(A_n)$ be a positive sequence with $\log_2 A_n/n\to0$. There are a randomized program $P$, a function $g$ with $g(n)/n\to0$, an integer $K$ and a constant $c>0$ with the following property. For every $n\ge1$ and every $B\in\mathrm{inputs}(n)$ whose lattice $L=L(B)$ satisfies the point-count bound (2.3),
--   $$N_L(r\lambda_1(L))\le A_n2^{\beta n}r^n\qquad(r\ge1),$$
--   $P$ halts on every coin tape within bit time $2^{(\beta+\frac12\log_2(4/3))n+g(n)}(\ell+1)^K$ and bit space $(4/3)^{n/2+g(n)}(\ell+1)^K$. With probability at least $c$, it outputs the coefficient vector of a shortest nonzero vector of $L$.
--   2. **On every lattice (4.23).** There are $P$, $g$ with $g(n)/n\to0$, $K$ and $c>0$ such that for every $n\ge1$ and every $B\in\mathrm{inputs}(n)$ the same holds without any condition on $L(B)$, with
--   $$T=\Big(\frac{8e}{3\pi}\Big)^{n/2+g(n)},\qquad S=\Big(\frac43\Big)^{n/2+g(n)} .$$
--
--   Here $N_L(R)$ counts the nonzero lattice vectors of length at most $R$, and $\lambda_1(L)$ is the length of a shortest nonzero vector. The second clause trades time for space: it uses less space than the mission's goal (Corollary 1.5), $(4/3)^{n/2}$ against $(8e/(3\pi))^{n/4}$.
--
--   **Formalization Note** Costs are bit time and bit space of the published randomized log-cost rational RAM `TwMSOCount.Main`, and success is `SolvesSVPWithProb`. The program, $g$, $K$ and $c$ are chosen after $\beta$ and $A$ and before $n$ and $B$.
--
--   Differences from the source:
--   - reading: "time" and "space" of an algorithm (no machine named) → bit time and bit space of the randomized log-cost RAM TwMSOCount.Main on every coin tape, times (ℓ+1)^K; reason: exact exponents need a random-access machine; "on every tape" is the stronger reading; the poly(ℓ) factor is the paper's implicit dependence on the input bit length (p.14).
--   - reading: "with constant probability"; the "in particular" clause (4.23) states no probability → one constant c > 0 fixed with the program, before n and B, for both clauses; reason: (4.23) is the specialization β = ½log₂(2e/π) (Theorem A.1) of the first clause, so it inherits its probability.
--   - encoding: a family of lattices satisfying (2.3) with A_n = 2^{o(n)} → every input basis whose lattice satisfies (2.3) for a fixed sequence A with A_n > 0 and log₂A_n/n → 0; reason: the family is the set of lattices obeying the bound, as in the published theorem_4_14.
--   - reading: the §4.2 algorithm takes det L = 1 and an estimate λ with λ1(L) ≤ λ ≤ (1+n^{−2})λ1(L) (p.38) → neither is assumed: the input is any invertible rational basis; reason: Theorem 4.9 is stated for lattices, not for normalized inputs with side information; the scaling and the polynomially many guesses (Lemma 2.8) are part of the algorithm.
--   - encoding: an input lattice given by a basis → an invertible rational basis B, input word n then B row by row, output the integer coefficient vector; reason: algorithm inputs are finite words.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.2, p.38 (PDF p.38), Theorem 4.9, eq. (4.23); (2.3), p.14; proof p.39

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_Supplement_SolvesSVPWithProb

open Filter

namespace SuperlatSVP.Supplement

/-- Theorem 4.9 (Quadratic-search SVP). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the
shortest vector problem and discrete Gaussian sampling*, STOC 2027 submission (manuscript sha256
fcf5b14f…ba), §4.2, p.38 (PDF p.38): "For a family of n-dimensional lattices satisfying the
point-count bound (2.3) with β ≥ 1/2 log2(4/3), there exists a randomized algorithm solving SVP
with constant probability in time 2^{(β+1/2 log2(4/3))n+o(n)} and space (4/3)^{n/2+o(n)}. In
particular, there exists a randomized algorithm solving SVP for any n-dimensional lattice in time
and space T = (8e/(3π))^{n/2+o(n)} = 2^{0.6031...n+o(n)}, S = (4/3)^{n/2+o(n)} = 2^{0.2075...n+o(n)}.
(4.23)"

**Formalization Note.** Both clauses are stated. (1) The family is every input lattice satisfying
(2.3) with a prefactor sequence `A` (`A_n > 0`, `log₂ A_n / n → 0`), as in the published
`SuperlatSVP.theorem_4_14`; there is no upper bound on `β`. One program `P`, one `g` with
`g(n)/n → 0` (time and space), one exponent `K` and one success probability `c > 0` are chosen
after `β, A` and before `n` and the basis. (2) For every lattice: one `P, g, K, c > 0`, time
`(8e/(3π))^{n/2+g(n)}` and space `(4/3)^{n/2+g(n)}`, with the closed forms of (4.23), not the
decimals. Inputs are invertible rational bases (input word: `n`, then `B` row by row); costs are
the bit time and bit space of the randomized log-cost RAM `TwMSOCount.Main` on every coin tape,
with the factor `(ℓ+1)^K` for the input length `ℓ` (`SolvesSVPWithProb`). -/
theorem theorem_4_9 :
    (∀ β : ℝ, (1 / 2) * Real.logb 2 (4 / 3) ≤ β →
      ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
        Tendsto (fun n : ℕ => Real.logb 2 (A n) / n) atTop (nhds 0) →
        ∃ (P : TwMSOCount.Main.Program) (g : ℕ → ℝ) (K : ℕ) (c : ℝ), 0 < c ∧
          Tendsto (fun n : ℕ => g n / n) atTop (nhds 0) ∧
          ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
            PointCountBound (lat (B.map (fun q : ℚ => (q : ℝ)))) A β →
              SolvesSVPWithProb P K
                ((2 : ℝ) ^ ((β + (1 / 2) * Real.logb 2 (4 / 3)) * n + g n))
                ((4 / 3 : ℝ) ^ ((n : ℝ) / 2 + g n)) c B) ∧
    (∃ (P : TwMSOCount.Main.Program) (g : ℕ → ℝ) (K : ℕ) (c : ℝ), 0 < c ∧
      Tendsto (fun n : ℕ => g n / n) atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        SolvesSVPWithProb P K
          ((8 * Real.exp 1 / (3 * Real.pi)) ^ ((n : ℝ) / 2 + g n))
          ((4 / 3 : ℝ) ^ ((n : ℝ) / 2 + g n)) c B) := by sorry

end SuperlatSVP.Supplement
