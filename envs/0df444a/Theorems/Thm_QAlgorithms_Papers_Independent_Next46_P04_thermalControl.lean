-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_thermalControl
-- name    : QAlgorithms.Papers.Independent.Next46.P04.thermalControl
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:41:21.814304+00:00
-- url     : https://prove2.me/theorems/398d6a52-11be-4464-82ba-392d6615710a
-- title:
--   Scalar thermal control criterion and crossover temperature
-- statement:
--   Work in the reduced, dispersionless conformal acoustic model with instantaneous quench and no backscattering. Let $V<0$, $a=|V|$, $c_{\rm in}>a$, $\kappa,n,\ell_\perp,m,\hbar,k_B>0$, and $n_1=n\ell_\perp^2$. The constant flow is $V$ and
--   $$c(x)=a\left(1+\frac23\tanh z(x)\right),\qquad z(x)=\frac{3\kappa x}{2a}.$$
--   The assertions are exact within this reduced model; they give no microscopic approximation error. No physical value of the discontinuous quench at $t=0$ is assigned.
--
--   For finite $T>0$, set $T_H=\hbar\kappa/(2\pi k_B)$, $A=3\kappa(a-c_{\rm in})/(2a)$, and $A_u=\pi k_BT(c_{\rm in}-a)/(\hbar c_{\rm in})$. Define
--   $$\rho_0(t,x)=e^{-\kappa t}\sinh\frac{3\kappa|x|}{2a},\qquad \rho_T(t,x)=\frac{\pi k_BT(c_{\rm in}-a)}{|A|\hbar c_{\rm in}}\rho_0(t,x).$$
--   Then
--   $$q:=\frac{A_u}{|A|}=\frac{aT}{3c_{\rm in}T_H},\qquad \rho_T=q\rho_0,\qquad q>1\iff T>\frac{3c_{\rm in}}aT_H.$$
--   For every $\delta>0$ and every real $t,x$,
--   $$\rho_T(t,x)<\delta\iff\rho_0(t,x)<\delta/q.$$
--   Above the crossover, $\delta/q<\delta$. At each fixed $x$, both control parameters tend to zero as $t\to+\infty$. These are exact scalar reformulations of the displayed control condition, not an observable detection rule, an error guarantee, or a peak-length theorem.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 5, Thermal late-time condition, continued from p. 4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF pp. 4--5, displayed scalar late-time conditions: exact coefficient,
crossover temperature, cutoff equivalence, and pointwise vanishing. The symbol
'much less than' is not upgraded to an error bound or an observed peak length. -/
theorem thermalControl (p : AcousticModel) (T : ℝ) (hT : 0 < T) :
    Au p T / |A p| = a p * T / (3 * p.cin * hawkingTemperature p) ∧
    (1 < Au p T / |A p| ↔ (3 * p.cin / a p) * hawkingTemperature p < T) ∧
    (∀ t x : ℝ, rhoT p T t x = (Au p T / |A p|) * rho0 p t x) ∧
    (∀ delta : ℝ, 0 < delta →
      (∀ t x : ℝ, rhoT p T t x < delta ↔
        rho0 p t x < delta / (Au p T / |A p|)) ∧
      ((3 * p.cin / a p) * hawkingTemperature p < T →
        delta / (Au p T / |A p|) < delta)) ∧
    (∀ x : ℝ, Tendsto (fun t => rho0 p t x) atTop (nhds 0) ∧
      Tendsto (fun t => rhoT p T t x) atTop (nhds 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
