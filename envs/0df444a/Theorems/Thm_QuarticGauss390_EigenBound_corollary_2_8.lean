-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_corollary_2_8
-- name    : QuarticGauss390.EigenBound.corollary_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:23.815195+00:00
-- url     : https://prove2.me/theorems/221e275c-dec2-4591-8dbd-2dda34c3c495
-- title:
--   Corollary 2.8 — $e^{zQ_x}$ maps the Gaussian cone into itself
-- statement:
--   Let $\mathcal C_G$ be the cone of complex multiples of pure Gaussian states (including $0$) for a CAR system on $n\ge2$ modes. For every $x\in\mathbb R^E$ and every $z\in\mathbb C$, the operator $e^{zQ_x}$, with $Q_x=\sum_px_pq_p$, satisfies
--   $$e^{zQ_x}\,\mathcal C_G\subseteq\mathcal C_G .$$
--
--   Exponentials of quadratic Majorana Hamiltonians, including non-unitary ones, therefore keep Gaussian vectors Gaussian up to scaling; Lemma 3.1 uses this for a variational argument inside the cone.
--
--   Differences from the source:
--   - encoding: $e^{zQ_x}$ → the matrix exponential `NormedSpace.exp (z • Q_x)`; "maps $\mathcal C_G$ into itself" → for every $v\in\mathcal C_G$, $e^{zQ_x}v\in\mathcal C_G$; reason: same operator and same statement
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.9, Corollary 2.8; cone defined p.8, Definition 2.4

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Gaussian
import Definitions.Def_QuarticGauss390_EigenBound_Moments

open Matrix

namespace QuarticGauss390.EigenBound

/-- Corollary 2.8, p.9: for every `x ∈ ℝ^E` and `z ∈ ℂ`, `e^{z Q_x}` maps the Gaussian
cone `𝒞_G` into itself. -/
theorem corollary_2_8 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (x : Pair n → ℝ) (z : ℂ)
    (v : Vec n) (hv : InGaussianCone C v) :
    InGaussianCone C (NormedSpace.exp (z • quadHam C x) *ᵥ v) := by sorry

end QuarticGauss390.EigenBound
