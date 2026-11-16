-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_Supplement_theorem_5_2
-- name    : QAdvFew.PoQOracle.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:24:34.908673+00:00
-- url     : https://prove2.me/theorems/eefdd90d-9606-420a-8d6f-2b1ec9cc367e
-- title:
--   Theorem 5.2 — simulating level $n$ of the oracle from $\mathrm{aux}_{\mathrm{RO}_n}$
-- statement:
--   Let $p,q:\mathbb N\to\mathbb N$ be computable with $p(n),q(n)\ge1$ for all $n$ and $p(n),q(n)<2^{n/8}$ for all sufficiently large $n$, and fix a PSPACE-complete oracle. Then there are a computable $L$ with $L(n)<P(n,p(n),q(n))$ for some polynomial $P$, a simulator $\mathrm{Sim}_{\mathrm{aux}}$, a constant $c>0$ and $n_0$ such that for every $n\ge n_0$, with probability at least $1-2^{-cn^2}$ over level $n$ of $\mathcal D$ ($\mathrm{RO}_n$, $\mathrm{SG}_n$, $\mathrm{Expand}_n$, $\mathrm{Mix}_n$), every oracle circuit $A^{(\cdot),\mathsf{PSPACE}}$ of size at most $q(n)$ satisfies
--
--   $$
--   \Bigl|\Pr\bigl[A^{\mathrm{SG}_n,\mathrm{Expand}_n,\mathrm{Mix}_n,\mathsf{PSPACE}}(\mathrm{RO}_n)\to1\bigr]-\Pr\bigl[A^{\mathrm{Sim}_{\mathrm{aux}}(\mathrm{aux}_{\mathrm{RO}_n}),\mathsf{PSPACE}}(\mathrm{RO}_n)\to1\bigr]\Bigr|\le\frac1{p(n)},
--   $$
--
--   where $A$ receives the entire truth table of $\mathrm{RO}_n$ as input and $\mathrm{aux}_{\mathrm{RO}_n}$ uses $L(n)$ samples. The simulator is inefficient and fixed before the oracle; the circuit $A$ may depend on the oracle (non-uniform classical advice).
--
--   This is the paper's key simulation step: an oracle algorithm with classical advice cannot tell level $n$ of the oracle from a simulator that sees only polynomially many samples, which is what makes $\mathsf{QCMA}$ verifiers simulable without the oracle.
--
--   Differences from the source:
--   - generalization: p(n), q(n) ≥ 1 with q(n) < 2^{n/8} and p(n) < 2^{n/8} (for every n) → p, q ≥ 1 for every n, and p, q < 2^{n/8} only for all sufficiently large n; reason: read for every n the hypotheses are unsatisfiable at n = 0 (2^0 = 1), which would make the theorem vacuous; the conclusion only concerns large n, and the eventual hypothesis covers every satisfiable reading, so the Lean statement specializes to the source's claim
--   - reading: with probability ≥ 1 − 2^{−Ω(n²)} → ∃ c > 0 (after p, q) and the bound 1 − 2^{−c n²} on the levelMeasure n (outer) measure; reason: standard meaning of Ω; c may depend on p, q
--   - reading: "with probability … the following holds … Then, for all sufficiently large n" → ∃ n₀, ∀ n ≥ n₀, Pr over level n [∀ A of size ≤ q(n): |…| ≤ 1/p(n)] ≥ 1 − 2^{−c n²}; reason: the circuit A is chosen inside the probability (it may depend on the oracle); the threshold on n is outside it
--   - reading: p(n), q(n) ≥ 1 computable functions; L(n) < poly(n, p(n), q(n)) → p, q : ℕ → ℕ with Mathlib Computable; L computable with L(n) < P(n, p(n), q(n)) for a polynomial P ∈ ℕ[X₀, X₁, X₂]; reason: computable functions on ℕ
--   - encoding: a stateful, inefficient simulator Sim_aux receiving aux_{RO_n} → an internal register initialized to (an init unitary applied to) aux_{RO_n} ⊗ |0⟩, with fixed unitaries for each component, level and direction, and for controlled queries; reason: every channel is a unitary with fresh ancillas (Stinespring); aux is the average over K, J of a pure state with a fixed layout
--   - encoding: A^{(·),PSPACE}(RO_n), an oracle circuit of size ≤ q(n) given the entire truth table → TTCirc n: the truth table (ordered by the binary value of (x, y), then output bit) on the first input wires, queries only to level n of SG, Expand, Mix, gates for Lps; size = binary description length plus n per query; reason: Lean representation of the paper's circuits and of "size = description length"
--   - encoding: a fixed oracle PSPACE for a PSPACE-complete problem (§5.1) → every PSPACE-complete language Lps (∀ Lps, as the classical oracle x ↦ [x ∈ Lps]); reason: the paper fixes an arbitrary such oracle; stating it for every choice is the same claim
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 5.2, p. 34 (PDF p. 36), with aux_{RO_n} defined on pp. 33–34 (PDF pp. 35–36)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_SimAux
import Definitions.Def_QAdvFew_PoQOracle_Supplement_IsPSPACEComplete

open QAlgorithms.Complexity MeasureTheory

namespace QAdvFew.PoQOracle.Supplement

/-- **Theorem 5.2** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 5.2, p. 34 (PDF p. 36)): "Let `p(n), q(n) ≥ 1` be any computable
functions such that `q(n) < 2^{n/8}` and `p(n) < 2^{n/8}`. There exists a simulator `Sim_aux` and a
computable function `L(n)` such that with probability `≥ 1 − 2^{−Ω(n²)}` over the choice of oracle
`SG_n, Mix_n, Expand_n`, the following holds. Let `A^{(·),PSPACE}` be any oracle circuit of size at
most `q(n)` … Then, for all sufficiently large `n`, `|Pr[A^{SG_n,Expand_n,Mix_n,PSPACE}(RO_n) → 1] −
Pr[A^{Sim_aux(aux_{RO_n}),PSPACE}(RO_n) → 1]| ≤ 1/p(n)` where `RO_n` corresponds to the entire truth
table of the random function `RO_n` used by the oracle. Furthermore, we have that
`L(n) < poly(n, p(n), q(n))` although `Sim_aux` itself is inefficient."

For every PSPACE-complete `Lps` and computable `p, q : ℕ → ℕ` with `1 ≤ p, q`, and `p, q < 2^{n/8}` for
all sufficiently large `n`: there are a
computable `L` with `L(n) < P(n, p(n), q(n))` for a polynomial `P`, a simulator `Sim` (receiving
`aux_{RO_n}` with `L(n)` samples), a constant `c > 0` and `n₀` such that for every `n ≥ n₀`, the
level-`n` sample `s` satisfies, with probability at least `1 − 2^{−c n²}`: every valid circuit `A`
(queries to level `n` of `SG, Expand, Mix` only, gates for `Lps`) of size at most `q(n)`, given the
truth table of `RO_n` as input, has `|realAcc − simAcc| ≤ 1/p(n)`.

**Formalization Note** The bounds `q(n), p(n) < 2^{n/8}` are assumed for all sufficiently large `n`:
assumed for every `n` together with `p, q ≥ 1` they are unsatisfiable at `n = 0` (`2^0 = 1`), which
would make the theorem vacuous; the conclusion only concerns large `n`. `2^{−Ω(n²)}` is read as `2^{−c n²}` for a constant `c > 0` chosen after `p, q`.
The simulator is chosen before the oracle and sees it only through `aux_{RO_n}`; the circuit `A` is
chosen after it (inside the probability), so it may depend on the oracle ("`A` implicitly gets
non-uniform classical advice on the oracle"). "Size" is description length in bits (§3.2.1) plus
`t` per level-`t` query. The probability is the (outer) `levelMeasure n`-measure. -/
theorem theorem_5_2 (Lps : Set Str) (hL : IsPSPACEComplete Lps) (p q : ℕ → ℕ)
    (hp : Computable p) (hq : Computable q) (hp1 : ∀ n, 1 ≤ p n) (hq1 : ∀ n, 1 ≤ q n)
    (hqb : ∀ᶠ n in Filter.atTop, (q n : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 8))
    (hpb : ∀ᶠ n in Filter.atTop, (p n : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 8)) :
    ∃ (L : ℕ → ℕ) (Sim : Simulator L), Computable L ∧
      (∃ P : MvPolynomial (Fin 3) ℕ, ∀ n, L n < MvPolynomial.eval ![n, p n, q n] P) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ENNReal.ofReal (1 - (2 : ℝ) ^ (-(c * (n : ℝ) ^ 2))) ≤
          levelMeasure n {s | ∀ A : TTCirc n, A.Valid → A.circ.size ≤ q n →
            |realAcc s (langOracle Lps) A - simAcc s (langOracle Lps) Sim A| ≤ 1 / (p n : ℝ)} := by sorry

end QAdvFew.PoQOracle.Supplement
