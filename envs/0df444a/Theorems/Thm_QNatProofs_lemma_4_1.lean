-- Prove2me | Theorems.Thm_QNatProofs_lemma_4_1
-- name    : QNatProofs.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:06:02.039078+00:00
-- url     : https://prove2.me/theorems/33d14836-8dc4-453f-90e1-682ed9f1dce9
-- title:
--   Lemma 4.1 — complex Gaussian sampler in MH
-- statement:
--   There are a QNC$^0$ depth $D$, a polynomial $p$ and one classical machine $M$ such that for every target error $\varepsilon\in(0,1)$ and failure probability $\eta\in(0,1)$, with $L=\lceil\log_2(1/\varepsilon)\rceil+\lceil\log_2(1/\eta)\rceil$, there is an $(s,\varepsilon,\eta)$-complex Gaussian sampler $\mathrm{Samp}:\{0,1\}^R\to\{0,1\}^{2q}$ for a known rescaling factor $s>0$ such that:
--
--   1. its tape length $R$ and output length $2q$ are at most $p(L)$;
--   2. its classical evaluation time is at most $p(L)$: $M$ computes $\mathrm{Samp}(\omega)$ from a description of length at most $p(L)$ and the tape $\omega$ within $p(L)$ steps;
--   3. it has an exact nonclean coherent implementation in $A_8CQ$ of size at most $p(L)$;
--   4. $s=\sqrt\mu$ for a natural number $\mu\le p(L)$, and every output has magnitude strictly less than one (p.25).
--
--   This is the sampler of the PRAL construction.
--
--   Differences from the source:
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - encoding: A₈CQ with constant depth; polynomial in log(1/ε) + log(1/η) and poly(log(1/ε), log(1/η)) → MHLevel 8 D for one D; one polynomial p evaluated at L = ⌈log₂(1/ε)⌉ + ⌈log₂(1/η)⌉ for all four bounds; reason: a polynomial in the two logarithms is bounded by a polynomial in their sum
--   - reading: classical evaluation time polynomial in log(1/ε) + log(1/η) → one FinTM2 machine M evaluates every sampler of the family within p(L) steps, from a description string of length ≤ p(L) and the tape; reason: the sampler is indexed by real ε, η, so uniformity needs a finite description; the description has polynomial length
--   - generalization: a known rescaling factor s > 0 → s = √µ with µ ∈ ℕ, µ ≤ p(L), and every output of magnitude < 1; reason: the two facts the proof and the paragraph on p.25 add; dropping them gives the printed statement
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Lemma 4.1, p.18; proof p.25; 'Compatibility with security parameters', p.25

import Mathlib
import Definitions.Def_QNatProofs_MHLevel
import Definitions.Def_QNatProofs_pralFamily

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms Polynomial

/-- **Lemma 4.1 (Complex Gaussian sampler in MH)** (Li, Parham, *Natural proofs for quantum state
preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.18): "For any target
approximation error `ε ∈ (0, 1)` and failure probability `η ∈ (0, 1)`, there exists an
`(s, ε, η)`-complex Gaussian sampler in the sense of Definition 3.1, for a known rescaling factor
`s > 0`. Its random-tape length, output length, and classical evaluation time are polynomial in
`log(1/ε) + log(1/η)`. Moreover, it has an exact nonclean coherent implementation in
`A₈CQ ⊆ MH₈` of size `poly(log(1/ε), log(1/η))`."

With `L = ⌈log₂(1/ε)⌉ + ⌈log₂(1/η)⌉`, one polynomial `p` bounds the tape length `R`, the output
length `2q` and the size of the coherent implementation, and one machine `M` evaluates every
sampler of the family in time `p(L)` from a description `z` of length at most `p(L)`.

**Formalization Note** `A₈CQ` is `MHLevel 8 D` for one absolute depth `D`. The conclusion also
records the two facts the paragraph "Compatibility with security parameters" (p.25) adds: the
rescaling factor is `s = √µ` for a natural number `µ ≤ p(L)` (so `γ² = 1/(4µ)` is rational), and
every output has magnitude strictly less than one. -/
theorem lemma_4_1 : ∃ (D : ℕ) (p : ℕ[X]) (M : Turing.TM2ComputableAux Bool Bool),
    ∀ ε η : ℝ, 0 < ε → ε < 1 → 0 < η → η < 1 →
    ∃ (R q : ℕ) (Samp : Sampler R q) (s : ℝ) (z : List Bool),
      IsComplexGaussianSampler s ε η Samp ∧
      R ≤ p.eval (⌈Real.logb 2 (1 / ε)⌉₊ + ⌈Real.logb 2 (1 / η)⌉₊) ∧
      2 * q ≤ p.eval (⌈Real.logb 2 (1 / ε)⌉₊ + ⌈Real.logb 2 (1 / η)⌉₊) ∧
      z.length ≤ p.eval (⌈Real.logb 2 (1 / ε)⌉₊ + ⌈Real.logb 2 (1 / η)⌉₊) ∧
      (∀ ω : Fin R → Bool, MachineComputesIn M (PPADSIS.SubexpSIS.encStr z ++ List.ofFn ω)
        (List.ofFn (Samp ω).1 ++ List.ofFn (Samp ω).2)
        (p.eval (⌈Real.logb 2 (1 / ε)⌉₊ + ⌈Real.logb 2 (1 / η)⌉₊))) ∧
      (∃ (nanc : ℕ) (U : Circuit allGates (R + (q + q + nanc))), U ∈ MHLevel 8 D _ ∧
        IsNoncleanEval (r := q + q) (w := nanc) U.unitary (fun ω => Fin.append (Samp ω).1 (Samp ω).2) ∧
        U.size ≤ p.eval (⌈Real.logb 2 (1 / ε)⌉₊ + ⌈Real.logb 2 (1 / η)⌉₊)) ∧
      (∃ mu : ℕ, s = Real.sqrt mu ∧ mu ≤ p.eval (⌈Real.logb 2 (1 / ε)⌉₊ + ⌈Real.logb 2 (1 / η)⌉₊)) ∧
      (∀ ω : Fin R → Bool, ‖polarVal (Samp ω)‖ < 1) := by sorry

end QNatProofs
