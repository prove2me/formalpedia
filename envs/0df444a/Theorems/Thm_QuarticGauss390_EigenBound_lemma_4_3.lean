-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_lemma_4_3
-- name    : QuarticGauss390.EigenBound.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:21.028025+00:00
-- url     : https://prove2.me/theorems/582dce33-4ae8-440f-a503-1180daea334c
-- title:
--   Lemma 4.3 — $\|M^{\rho_1}-M^{\rho_2}\|_{\mathrm{op}}\le2\Rightarrow\|M^{\rho_1}-M^{\rho_2}\|_F\le5\sqrt{6n}$
-- statement:
--   Fix a CAR system on $n\ge2$ modes. For density matrices $\rho_1,\rho_2$,
--   $$\|M^{\rho_1}-M^{\rho_2}\|_{\mathrm{op}}\le2\ \Longrightarrow\ \|M^{\rho_1}-M^{\rho_2}\|_F\le5\sqrt{6n}.$$
--
--   For moment matrices of physical states, an operator-norm bound gives a Frobenius-norm bound with only a $\sqrt n$ loss, much better than the generic factor $\sqrt m$ with $m=\binom{2n}2$.
--
--   Differences from the source:
--   - encoding: $\|\cdot\|_{\mathrm{op}}$, $\|\cdot\|_F$ → norm of the matrix as a linear map on Euclidean space, and $(\sum_{p,r}D_{pr}^2)^{1/2}$; reason: the source's norms
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.15, Lemma 4.3

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Moments
import Definitions.Def_QuarticGauss390_EigenBound_MatrixNorms

open Matrix

namespace QuarticGauss390.EigenBound

/-- Lemma 4.3, p.15: for density matrices `ρ₁, ρ₂`,
`‖M^{ρ₁} - M^{ρ₂}‖_op ≤ 2 ⟹ ‖M^{ρ₁} - M^{ρ₂}‖_F ≤ 5√(6n)`. -/
theorem lemma_4_3 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (ρ₁ ρ₂ : Op n)
    (h₁ : IsDensity ρ₁) (h₂ : IsDensity ρ₂)
    (hop : opNorm (momentMatrix C ρ₁ - momentMatrix C ρ₂) ≤ 2) :
    frobNorm (momentMatrix C ρ₁ - momentMatrix C ρ₂) ≤ 5 * Real.sqrt (6 * n) := by sorry

end QuarticGauss390.EigenBound
