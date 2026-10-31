-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_brownianDiffusion_minimum
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.brownianDiffusion_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:25:33.29608+00:00
-- url     : https://prove2.me/theorems/e1d7f403-7897-414c-85bf-1675708a2500
-- title:
--   §5.3.1: Brownian diffusion coefficients attain the CP boundary, (5.16)–(5.20)
-- statement:
--   Let $M,\beta,\hbar>0$ and $\eta\ge0$. Put $D_{pp}=\eta M/\beta$ and $D_{xx}=\eta\beta\hbar^2/(16M)$. Then
--   $$
--   D_{xx}=\left(\frac{\beta\hbar}{4M}\right)^2D_{pp},\qquad D_{xx}D_{pp}=\frac{\eta^2\hbar^2}{16}.
--   $$
--   Also $D_{pp}=\eta\langle |P|^2\rangle_\beta/3$ for the normalized Maxwell tracer law, and $D_{xx}=\eta\lambda_{\rm th}^2/(32\pi)$ with $\lambda_{\rm th}=\sqrt{2\pi\hbar^2\beta/M}$. Among all nonnegative $d$ satisfying $dD_{pp}\ge\eta^2\hbar^2/16$, $D_{xx}$ is the least. This includes $\eta=0$, when the minimum is zero. The generic complete-positivity characterization is cited background.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 28, §5.3.1: Brownian diffusion coefficients attain the CP boundary, (5.16)–(5.20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.28–29, (5.16)–(5.20): saturation and the actual minimum among
nonnegative admissible Dxx, including eta=0. Generic CP characterization is
cited background, not a new equivalence theorem here. -/
theorem brownianDiffusion_minimum (M beta hbar eta : ℝ)
    (hM : 0 < M) (hbeta : 0 < beta) (hhbar : 0 < hbar) (heta : 0 ≤ eta) :
    positionDiffusion M beta hbar eta = (beta * hbar / (4 * M)) ^ 2 * momentumDiffusion M beta eta ∧
    positionDiffusion M beta hbar eta * momentumDiffusion M beta eta = eta ^ 2 * hbar ^ 2 / 16 ∧
    momentumDiffusion M beta eta = eta / 3 *
      (∫ P : Momentum, ‖P‖ ^ 2 * maxwell M beta P) ∧
    positionDiffusion M beta hbar eta = eta / (32 * Real.pi) *
      Real.sqrt (2 * Real.pi * hbar ^ 2 * beta / M) ^ 2 ∧
    0 ≤ positionDiffusion M beta hbar eta ∧
    (∀ Dxx : ℝ, 0 ≤ Dxx →
      eta ^ 2 * hbar ^ 2 / 16 ≤ Dxx * momentumDiffusion M beta eta →
      positionDiffusion M beta hbar eta ≤ Dxx) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
