-- Prove2me | Theorems.Thm_PRUMicrocrypt_theorem_4_1
-- name    : PRUMicrocrypt.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:51.660222+00:00
-- url     : https://prove2.me/theorems/4aedad51-19f7-432d-93a9-9c4c13fc0a0c
-- title:
--   Theorem 4.1 — independent-hidden-phase security: $|\mathbb E_S\Pr[A^{U(S)}=1]-\mathbb E_V\Pr[A^V=1]|=O(t^2N^{-1/8})$
-- statement:
--   There is a universal constant $C$ with the following property. Let $N=2^n$, let the five phase tables $S=(h_1,\dots,h_5)$ be independent uniform functions $\mathbb F_2^n\to\mathbb Z_N$, and let $A$ make $t\ge1$ queries to $\mathrm{Select}(\cdot)$ in the model of Section 3. If
--
--   $$3(2t)^{16}\le N,$$
--
--   then
--
--   $$\Big|\mathbb E_S\big[\Pr[A^{U(S)}=1]\big]-\mathbb E_{V\leftarrow\mathrm{Haar}(U(N))}\big[\Pr[A^V=1]\big]\Big|\le C\,t^2N^{-1/8}.$$
--
--   So five independent random phase layers interleaved with Hadamards form a strong pseudorandom unitary against adaptive, coherently controlled queries to $U,U^\dagger,U^T,\overline U$. Lemma 5.4 is combined with this theorem to prove Theorem 5.3.
--
--   Differences from the source:
--   - encoding: Δ_t = O(t²N^{−1/8}) with universal implied constants (H.31) → ∃ C, chosen before n, t and the algorithm, with bound C t² N^{−1/8}; reason: the meaning of a universal O-constant
--   - generalization: Pr[A = 1] for an algorithm with a final output → acceptance ⟨ψ_t|E|ψ_t⟩ for an arbitrary effect 0 ≤ E ≤ I; reason: every final two-outcome measurement is an effect; measuring an output qubit is the special case
--   - encoding: inter-query isometries, selector projections, E_S, E_{V←Haar} → unitaries on ℂ⁵ ⊗ ℂᴺ ⊗ ℂ^W with P_a = |a⟩⟨a|, the uniform average over Fin 5 → Fin N → Fin N, the published unitaryHaar (2 ^ n); reason: the same algorithms and expectations
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Theorem 4.1, p.24; (H.31), p.90

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_PRUMicrocrypt_QueryAlg

set_option autoImplicit false

namespace PRUMicrocrypt

open MeasureTheory

/-- **Theorem 4.1 (Independent-hidden-phase security).** "Let N = 2^n, let the five hidden phase
tables be independent uniform functions to ℤ_N, and let A make t ≥ 1 unitary-oracle queries in the
model of Section 3. Assume 3(2t)^16 ≤ N. (4.4) Then
|E_S[Pr[A^{U(S)} = 1]] − E_{V←Haar(U(N))}[Pr[A^V = 1]]| ≤ Δ_t = O(t²N^{−1/8}). (4.5)"
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Theorem 4.1, p.24; "The implied constants are universal", (H.31), p.90.

**Formalization Note.** `O(t²N^{−1/8})` with a universal constant is `∃ C, … ≤ C t² N^{−1/8}` with
`C` chosen before `n`, `t` and the algorithm. An algorithm in the model of Section 3 is a
`QueryAlg` (unit initial vector, arbitrary finite reference, unitary inter-query operations) with
coherent access to `Select(U)` and a final two-outcome measurement, an effect `0 ≤ E ≤ I`.
`E_S` is the uniform average over five-table samples; Haar is the published `unitaryHaar (2 ^ n)`. -/
theorem theorem_4_1 : ∃ C : ℝ, ∀ n t : ℕ, 1 ≤ t → 3 * (2 * t) ^ 16 ≤ 2 ^ n →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (alg : QueryAlg n t W)
      (E : Matrix (Acc n W) (Acc n W) ℂ), IsEffect E →
      |tableAvg n (fun S => alg.accept E (phaseHadamardU S)) -
          ∫ V, alg.accept E (V : Matrix (Idx n) (Idx n) ℂ)
            ∂ QAlgorithms.Schur.unitaryHaar (2 ^ n)| ≤
        C * (t : ℝ) ^ 2 * ((2 : ℝ) ^ n) ^ (-(1 / 8 : ℝ)) := by sorry

end PRUMicrocrypt
