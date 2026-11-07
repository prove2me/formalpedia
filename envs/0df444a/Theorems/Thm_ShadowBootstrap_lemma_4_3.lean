-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_4_3
-- name    : ShadowBootstrap.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:47.504043+00:00
-- url     : https://prove2.me/theorems/58b59dd4-c603-450d-94dc-10d39fecb699
-- title:
--   Lemma 4.3 — $\mathbb E[\||e_t\rangle\|_2^2 \mid \sigma_{t-1}] \le \frac{2C}{N_t}(1 - \mathrm{Tr}(\psi\sigma_{t-1}) + \frac{d}{2S_t})$
-- statement:
--   Let $E$ be as in Lemma 4.2 (Clifford, invertible shadow channel, Eq. (8) with constant $C_F$) and $C = C_F + 1$. Let $|\psi\rangle$, $|\sigma_0\rangle$ and the current estimate $|\sigma_{t-1}\rangle$ be unit vectors, and $N_t, S_t \ge 1$. At stage $t$, draw $N_t$ independent bases from $E$, measure each on $S_t$ fresh copies of $|\psi\rangle$, form the residuals $\Delta_{t,i}$ with reference state $\sigma_{t-1}$, and let $|e_t\rangle$ be the error of Eq. (14). Then
--   $$\mathbb E\big[\||e_t\rangle\|_2^2 \,\big|\, \sigma_{t-1}\big] \le \frac{2C}{N_t}\Big(1 - \operatorname{Tr}(\psi\sigma_{t-1}) + \frac{d}{2S_t}\Big),\qquad \operatorname{Tr}(\psi\sigma_{t-1}) = |\langle\psi|\sigma_{t-1}\rangle|^2 .$$
--
--   Each stage therefore shrinks the error in proportion to the current infidelity plus a shot-noise term.
--
--   Differences from the source:
--   - reading: a Clifford ensemble satisfying Lemma 3.8 (Eq. (8)) → any finite ensemble whose positive-weight unitaries are Clifford, with invertible shadow channel, satisfying Var[Tr(Oρ̂)] ≤ C_F‖O‖_F² for every state and Hermitian O; reason: this is Definition 4.1's hypothesis; invertibility is presupposed by M⁻¹
--   - generalization: C = O(1) → the explicit constant C = C_F + 1; reason: the proof bounds the shot term by (1/S)‖Eρ̂²‖_op and ‖Eρ̂²‖_op ≤ (C_F + 1)d follows from (8) for any such ensemble; an explicit constant specializes to O(1)
--   - encoding: pure states ψ, σ₀, σ_{t−1} → unit vectors; Tr(ψσ) = |⟨ψ|σ⟩|²; frequencies from histograms; reason: the same objects
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 4.3, p.14, with Eqs. (12)–(14), p.14

import Mathlib
import Definitions.Def_ShadowBootstrap_stagesExpect
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 4.3, p.14 (with Eqs. (12)–(14)): for a fixed current estimate `σ_{t−1}`, the expectation
over the `N_t` bases and their outcomes at stage `t` satisfies
`E[‖|e_t⟩‖₂² | σ_{t−1}] ≤ (2C/N_t)(1 − Tr(ψσ_{t−1}) + d/(2S_t))`.

**Formalization Note** The ensemble is any finite Clifford ensemble with invertible shadow channel
satisfying Eq. (8) with constant `C_F` (Lemma 4.2's hypotheses), and `C = C_F + 1` is Lemma 4.2's
constant. `|e_t⟩ = ((1/N_t) Σ_i ∆_{t,i} − (ψ − σ_{t−1}))|σ₀⟩` (Eq. (14)); the `N_t` bases are
independent draws from `E`, each measured on `S_t` fresh copies of `|ψ⟩`. `ψ`, `σ₀`, `σ_{t−1}` are
unit vectors and `Tr(ψσ_{t−1}) = |⟨ψ|σ_{t−1}⟩|²`. -/
theorem lemma_4_3 (CF : ℝ) (n : ℕ) {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hCl : IsCliffordPrimitive E) (hinv : IsUnit (measChannel E))
    (hvar : ∀ ρ : Op n, WildeQIT.IsDensityOperator ρ → ∀ O : Op n, O.IsHermitian →
      snapVar E ρ O ≤ CF * frobSq O)
    (ψ σ₀ σprev : Bits n → ℂ) (hψ : IsUnitVec ψ) (hσ₀ : IsUnitVec σ₀) (hσ : IsUnitVec σprev)
    (N S : ℕ) (hN : 1 ≤ N) (hS : 1 ≤ S) :
    ∑ data : Fin N → ι × (Fin S → Bits n), stageWeight E ψ data *
        vnormSq (stageError ψ σ₀ σprev
          (stageCorrection E σprev S fun i => ((data i).1, histOf (data i).2)))
      ≤ 2 * (CF + 1) / N * (1 - ‖braket ψ σprev‖ ^ 2 + 2 ^ n / (2 * S)) := by sorry

end ShadowBootstrap
