-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_4_4
-- name    : ShadowBootstrap.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:56.917521+00:00
-- url     : https://prove2.me/theorems/33b0d3a6-1c24-47c4-bbda-4b31dbcbaf47
-- title:
--   Lemma 4.4 — $1 - \mathrm{Tr}(\psi\sigma_t) \le \||e_t\rangle\|_2^2/\mathrm{Tr}(\psi\sigma_0) \le 2\||e_t\rangle\|_2^2$
-- statement:
--   Let $|\psi\rangle$, $|\sigma_0\rangle$, $|\sigma_{t-1}\rangle$ be unit vectors with $\operatorname{Tr}(\psi\sigma_0) = |\langle\psi|\sigma_0\rangle|^2 \ge 1/2$, and let $D$ be any operator (in the paper $D = \frac{1}{N_t}\sum_i\Delta_{t,i}$). Define $|\sigma_t\rangle$ by Eqs. (12)–(13) with correction $D$ and $|e_t\rangle := (D - (\psi - \sigma_{t-1}))|\sigma_0\rangle$ (Eq. (14)). Then
--   $$1 - \operatorname{Tr}(\psi\sigma_t) \le \frac{\||e_t\rangle\|_2^2}{\operatorname{Tr}(\psi\sigma_0)} \le 2\||e_t\rangle\|_2^2. \tag{16}$$
--
--   This turns the vector error of a stage into the infidelity of its output, including the fallback case $|\tilde\sigma_t\rangle = 0$.
--
--   Differences from the source:
--   - generalization: D = (1/N_t) Σ_i ∆_{t,i} → any operator D; reason: the bound uses only identity (15), which holds for every D; the paper's D is a special case
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 4.4, Eq. (16), p.14, with Eqs. (12)–(15)

import Mathlib
import Definitions.Def_ShadowBootstrap_stagesExpect

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 4.4, Eq. (16), p.14: given `Tr(ψσ₀) ≥ 1/2`,
`1 − Tr(ψσ_t) ≤ ‖|e_t⟩‖₂² / Tr(ψσ₀) ≤ 2‖|e_t⟩‖₂²`.

**Formalization Note** `σ_t` is the stage update of Eqs. (12)–(13) and `|e_t⟩` the error of
Eq. (14), both built from the correction `D`; in the paper `D = (1/N_t) Σ_i ∆_{t,i}`, here `D` is
any operator. `ψ`, `σ₀`, `σ_{t−1}` are unit vectors and `Tr(ψσ) = |⟨ψ|σ⟩|²`. -/
theorem lemma_4_4 (n : ℕ) (ψ σ₀ σprev : Bits n → ℂ) (hψ : IsUnitVec ψ) (hσ₀ : IsUnitVec σ₀)
    (hσ : IsUnitVec σprev) (h0 : 1 / 2 ≤ ‖braket ψ σ₀‖ ^ 2) (D : Op n) :
    1 - ‖braket ψ (stageUpdate σ₀ σprev D)‖ ^ 2 ≤
        vnormSq (stageError ψ σ₀ σprev D) / ‖braket ψ σ₀‖ ^ 2 ∧
      vnormSq (stageError ψ σ₀ σprev D) / ‖braket ψ σ₀‖ ^ 2 ≤
        2 * vnormSq (stageError ψ σ₀ σprev D) := by sorry

end ShadowBootstrap
