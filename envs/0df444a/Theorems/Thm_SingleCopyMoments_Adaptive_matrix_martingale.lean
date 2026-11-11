-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_matrix_martingale
-- name    : SingleCopyMoments.Adaptive.matrix_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:33.57038+00:00
-- url     : https://prove2.me/theorems/9c8a9148-faa2-4589-a17c-6bf7496df4b6
-- title:
--   Lemma 35 — Martingale differences and uniform matrix bounds
-- statement:
--   In the physical latent domain $R_\theta<1/2$, with $0<\alpha\le1/100$ and $\kappa\ge1$, the raw and retained matrices both satisfy the conditional estimates
--
--   $$\mathbb E_\theta[Y_i\mid\mathcal F_{i-1}]=0,\quad\mathbb E_\theta[Y_i^2\mid\mathcal F_{i-1}]\preceq\frac2dI,\quad\mathbb E_\theta[|\operatorname{Tr}(MY_i)|^2\mid\mathcal F_{i-1}]\le\frac2d\|M\|_{HS}^2.$$
--
--   Here $M$ is any complex matrix determined by the past, without a Hermitian restriction. The conditional sigma-algebra contains the fixed latent vectors, seed, and preceding outcomes. The statement expresses these expectations as one-step Born-kernel integrals at each fixed latent vector and past; these integrands are integrable. Both choices of the raw/retained flag are included.
--
--   For every budget $T$, every record, and every subset $J$ of its rounds, only the retained matrices additionally satisfy
--
--   $$\left\|\sum_{i\in J}Y_i\right\|_{op}\le K=2(\kappa+2).$$
--
--   All constants are independent of the eventual small choice of $\alpha$. The subset bound retains the threshold-crossing round and places no restriction on $T$.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: conditioning on latent vectors, seed, and the past, for every predictable M → one-step Born-kernel integrals for every fixed latent vector, past, and complex matrix M; reason: this pointwise conditional-law formulation permits every predictable M without adding global boundedness or integrability assumptions on M
--   - generalization: conditional bounds under the original joint law → pointwise one-step kernel bounds for every physical latent vector and every past; reason: the source Born-kernel calculation uses only the physical floor and POVM completeness and therefore applies pointwise, implying its almost-everywhere conditional bounds
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 35, (7.23)–(7.26), printed p. 38 (PDF p. 40); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 35, printed pp.38–39 (PDF pp.40–41). Conditional expectations
are expressed by the one-step Born kernel at fixed latent vectors and past. -/
theorem matrix_martingale (d r : ℕ) (hd : 0 < d) (hr : 2 ≤ r)
    (α θ κ : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1/100) (hκ : 1 ≤ κ)
    (hθ : θ ∈ Set.Icc 0 (Real.pi/r)) (g : Latent d r) (hg : radial α θ g < 1/2)
    (P : Protocol d) (R : Refinement hd P) :
    (∀ (i : ℕ) (H : Record P) (b : Bool),
      let μ := P.step i (physicalInput hd α θ g, H)
      let Y := oneStepMatrix R α θ κ g i H b
      Integrable Y μ ∧ Integrable (fun y => Y y ^ 2) μ ∧
      (∫ y, Y y ∂μ) = 0 ∧
      Loewner (∫ y, Y y ^ 2 ∂μ) ((2/(d : ℝ)) • (1 : Op d)) ∧
      ∀ M : Op d, Integrable (fun y => ‖(M * Y y).trace‖^2) μ ∧
        (∫ y, ‖(M * Y y).trace‖^2 ∂μ) ≤ (2/(d : ℝ))*hsSq M) ∧
    (∀ (T : ℕ) (H : Record P) (J : Finset (Fin T)),
      opNorm (∑ i ∈ J, retainedMatrix α θ κ g (projectors R T H) i) ≤ matrixConstant κ) := by sorry

end SingleCopyMoments.Adaptive
