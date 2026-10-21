-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_normalizedNullCoordinates
-- name    : QAlgorithms.Papers.Independent.Next46.P04.normalizedNullCoordinates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:38:02.779527+00:00
-- url     : https://prove2.me/theorems/07b53d1f-b664-46d9-9a02-ba41900050c3
-- title:
--   Normalized initial and final null coordinates
-- statement:
--   Work in the reduced, dispersionless conformal acoustic model with instantaneous quench and no backscattering. Let $V<0$, $a=|V|$, $c_{\rm in}>a$, $\kappa,n,\ell_\perp,m,\hbar,k_B>0$, and $n_1=n\ell_\perp^2$. The constant flow is $V$ and
--   $$c(x)=a\left(1+\frac23\tanh z(x)\right),\qquad z(x)=\frac{3\kappa x}{2a}.$$
--   The assertions are exact within this reduced model; they give no microscopic approximation error. No physical value of the discontinuous quench at $t=0$ is assigned.
--
--   Write $u_{\rm in}(t,x)=t-x/(c_{\rm in}-a)$, $v_{\rm in}(t,x)=t+x/(c_{\rm in}+a)$, and
--   $$u(t,x)=t-\frac{\log\sinh z(|x|)}\kappa,\qquad v(t,x)=t+\frac{9\kappa x/(2a)-\log\cosh(z(x)+\operatorname{artanh}(1/3))}{8\kappa}.$$
--   The outgoing coordinate has domain $x\ne0$. Shell evaluations mean the smooth coordinate formulas at $t=0$, for matching only.
--
--   For $t<0$, the initial coordinate time derivatives equal one and their spatial derivatives are $-1/(c_{\rm in}-a)$ and $1/(c_{\rm in}+a)$. For $t>0$,
--   $$u_t=1,\quad u_x=-\frac1{c(x)-a}\quad(x\ne0),\qquad v_t=1,\quad v_x=\frac1{c(x)+a}\quad(x\in\mathbb R).$$
--   The displayed integration constants give $v(0,0)=-\log\cosh(\operatorname{artanh}(1/3))/(8\kappa)$. For the metric quadratic form $Q_x(\tau,\xi)=-(c(x)^2-a^2)\tau^2+2a\tau\xi+\xi^2$, both tangent vectors $(1,c(x)-a)$ and $(1,-(c(x)+a))$ are null. These facts characterize the normalized coordinates used for matching.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 2, (6),(9)--(10)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF p. 2, (6),(9)--(10): null-coordinate derivatives with the displayed
constants. The outgoing coordinate is only asserted off the horizon. -/
theorem normalizedNullCoordinates (p : AcousticModel) :
    (∀ t : ℝ, t < 0 → ∀ x : ℝ,
      HasDerivAt (fun r => initialU p r x) 1 t ∧
      HasDerivAt (initialU p t) (-1 / (p.cin - a p)) x ∧
      HasDerivAt (fun r => initialW p r x) 1 t ∧
      HasDerivAt (initialW p t) (1 / (p.cin + a p)) x) ∧
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, x ≠ 0 →
      HasDerivAt (fun r => u p r x) 1 t ∧
      HasDerivAt (u p t) (-1 / (soundSpeed p x - a p)) x) ∧
    (∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun r => v p r x) 1 t ∧
      HasDerivAt (v p t) (1 / (soundSpeed p x + a p)) x) ∧
    v p 0 0 = -Real.log (Real.cosh (Real.artanh (1 / 3 : ℝ))) / (8 * p.kappa) ∧
    (∀ x : ℝ, acousticForm p x 1 (soundSpeed p x - a p) = 0 ∧
      acousticForm p x 1 (-(soundSpeed p x + a p)) = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
