-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_fixed_gain_noise_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.fixed_gain_noise_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:08:49.864463+00:00
-- url     : https://prove2.me/theorems/d1e62af7-651f-4454-b41a-6cc18c1ec2da
-- title:
--   Optimal completely positive noise at fixed real gain
-- statement:
--   Let $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be a finite physical centered two-mode Gaussian resource. Let $D$ be either a physical pure-input covariance or the formal zero matrix for the process score. For every fixed real $2\times2$ gain $S$, define
--
--   $$M=2D+RAR^T+RCS^T+SC^TR^T+SBS^T,\qquad R=\operatorname{diag}(1,-1).$$
--
--   Then $M$ is positive definite. The noise
--
--   $$G_* = \frac{|1-\det S|}{\sqrt{\det M}}M$$
--
--   is admissible for a deterministic trace-preserving Gaussian channel and attains
--
--   $$\min_{G:\ G+i\Omega-iS\Omega S^T\succeq0}\det(M+G)=(|1-\det S|+\sqrt{\det M})^2,$$
--
--   where admissible $G$ is real symmetric and $\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. In particular, determinant-one gains allow $G_*=0$. This solves the noise optimization without assuming invertibility of $G$.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 4, §III, Eqs.(29)–(40)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.4, Eqs.(29)-(40): the displayed noise attains the minimum over
all admissible noises at each real gain S, including det S=1 and G=0. -/
theorem fixed_gain_noise_optimum (A B C D S : QuadratureMatrix)
    (hresource : PhysicalResource (resourceCov A B C)) (hD : InputOrProcess D) :
    let M := noiseBase D A B C S
    let G := (|1 - S.det| / Real.sqrt M.det) • M
    M.PosDef ∧ 0 < M.det ∧ GaussianCP S G ∧
    (M + G).det = reducedDet D A B C S ∧
    ∀ H : QuadratureMatrix, GaussianCP S H → (M + G).det ≤ (M + H).det := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
