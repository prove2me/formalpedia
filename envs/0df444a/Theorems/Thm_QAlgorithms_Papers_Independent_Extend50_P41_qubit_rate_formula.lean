-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_qubit_rate_formula
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.qubit_rate_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:39:12.308021+00:00
-- url     : https://prove2.me/theorems/5d0f5f7c-827e-45ea-9894-29381aa5d3a8
-- title:
--   Equation (29): explicit qubit rate
-- statement:
--   Let $\rho=(1+\mathbf x\cdot\boldsymbol\sigma)/2$ and $\sigma=(1+\mathbf y\cdot\boldsymbol\sigma)/2$ be qubit density matrices, where $\boldsymbol\sigma$ is the standard Pauli triple and the Bloch vectors have lengths $r=|\mathbf x|\le1$, $b=|\mathbf y|\le1$. Put $a=(\mathbf x\cdot\mathbf y)/b$ when $b>0$, and put $a=0$ when $b=0$. With von Neumann entropy $S_{\rm vN}$ in nats, the full rate is
--   $$\widehat I(\rho,\sigma)=-S_{\rm vN}(\sigma)-b\log\frac{1+a}{2}-\frac{1-b}{2}\log\frac{1-r^2}{4}.$$
--   For nonzero vectors $a=r\cos\theta$. Zero weights annihilate infinite logarithms, so pure states and zero Bloch vectors remain included. The formula specializes the principal-minor rate to dimension two.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 9, Equation (29)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, (29): explicit qubit rate, including zero Bloch vectors and pure
states. Dot(x,y)/|y| is r cos(theta) when |y|>0; its zero-weight extension needs
no angle restriction at |y|=0. -/
theorem qubit_rate_formula (rho sigma : DensityOutcome 2) (x y : Fin 3 → ℝ)
    (hx : blochLength x ≤ 1) (hy : blochLength y ≤ 1)
    (hrho : rho.val = blochDensityMatrix x) (hsigma : sigma.val = blochDensityMatrix y) :
    (fullRate rho sigma : EReal) =
      (-(vnEntropy sigma.val * Real.log 2) : ℝ) +
        weightedNegLog (blochLength y) ((1 + blochDirectionalComponent x y)/2) +
        weightedNegLog ((1 - blochLength y)/2) ((1 - (blochLength x)^2)/4) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
