-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_4_2
-- name    : ShadowBootstrap.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:21.019792+00:00
-- url     : https://prove2.me/theorems/4b2cbca0-4bb3-47b6-accf-2fc0ef757ec5
-- title:
--   Lemma 4.2 — residual mean $\rho - \sigma$ and variance $\le C(\|\rho-\sigma\|_F^2 + d/S)$
-- statement:
--   Let $E$ be a Clifford ensemble on $n$ qubits with invertible shadow channel satisfying Eq. (8) with constant $C_F$ for every state and Hermitian observable. Fix states $\rho, \sigma$ and a number of shots $S \ge 1$. Draw a basis $U \sim E$, take $S$ independent shots of $\rho$ in that basis with empirical frequencies $\hat f$, and form the residual estimator $\Delta$ of Eq. (10) with reference state $\sigma$. Then, with expectations over the basis and its $S$ outcomes,
--   $$\mathbb E[\Delta] = \rho - \sigma \qquad\text{and}\qquad \Big\|\mathbb E[\Delta^2] - (\mathbb E[\Delta])^2\Big\|_{op} \le C\Big(\|\rho-\sigma\|_F^2 + \frac dS\Big),\qquad C = C_F + 1,\ d = 2^n.$$
--
--   The variance floor is governed by the discrepancy $\rho - \sigma$, which is what lets the current estimate act as a control variate in the bootstrapping stages.
--
--   Differences from the source:
--   - reading: a Clifford ensemble satisfying Lemma 3.8 (Eq. (8)) → any finite ensemble whose positive-weight unitaries are Clifford, with invertible shadow channel, satisfying Var[Tr(Oρ̂)] ≤ C_F‖O‖_F² for every state and Hermitian O; reason: this is Definition 4.1's hypothesis; invertibility is presupposed by M⁻¹
--   - generalization: C = O(1) → the explicit constant C = C_F + 1; reason: the proof bounds the shot term by (1/S)‖Eρ̂²‖_op and ‖Eρ̂²‖_op ≤ (C_F + 1)d follows from (8) for any such ensemble; an explicit constant specializes to O(1)
--   - encoding: S shots → S ≥ 1; expectations as finite sums over the basis label and (bit strings)^S; reason: the same expectations
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 4.2, p.12, with Definition 4.1, Eq. (10), p.11

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ShadowBootstrap_residual
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 4.2, p.12 (with Definition 4.1, Eq. (10), p.11): for fixed states `ρ, σ`, the residual
estimator `∆` of a basis `U ∼ E` and `S` shots on `ρ` satisfies `E[∆] = ρ − σ` and
`‖E[∆²] − (E[∆])²‖_op ≤ C(‖ρ − σ‖_F² + d/S)`, `C = O(1)`, `d = 2ⁿ`.

**Formalization Note** The ensemble is any finite Clifford ensemble (`IsCliffordPrimitive`) with
invertible shadow channel satisfying Eq. (8) of Lemma 3.8 with constant `C_F` for every state and
Hermitian observable ("Let E be a Clifford ensemble satisfying Lemma 3.8", Definition 4.1); the
constant is the explicit `C = C_F + 1`. The expectation is the finite sum over the basis label and
the `S` independent outcomes on `ρ` (`resExpect`); the frequencies are `f̂(z) = #{a : b_a = z}/S`. -/
theorem lemma_4_2 (CF : ℝ) (n : ℕ) {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hCl : IsCliffordPrimitive E) (hinv : IsUnit (measChannel E))
    (hvar : ∀ ρ : Op n, WildeQIT.IsDensityOperator ρ → ∀ O : Op n, O.IsHermitian →
      snapVar E ρ O ≤ CF * frobSq O)
    (ρ σ : Op n) (hρ : WildeQIT.IsDensityOperator ρ) (hσ : WildeQIT.IsDensityOperator σ)
    (S : ℕ) (hS : 1 ≤ S) :
    resExpect E ρ S (fun i bs => residual E σ i (empFreq bs)) = ρ - σ ∧
      opNorm (resExpect E ρ S (fun i bs => residual E σ i (empFreq bs) * residual E σ i (empFreq bs))
          - resExpect E ρ S (fun i bs => residual E σ i (empFreq bs)) *
            resExpect E ρ S (fun i bs => residual E σ i (empFreq bs)))
        ≤ (CF + 1) * (frobSq (ρ - σ) + 2 ^ n / S) := by sorry

end ShadowBootstrap
