-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_stationaryVacuumCorrelator
-- name    : QAlgorithms.Papers.Independent.Next46.P04.stationaryVacuumCorrelator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:40:20.109974+00:00
-- url     : https://prove2.me/theorems/66557030-e531-4162-9b0c-2040f3dc1953
-- title:
--   Pointwise stationary vacuum correlator with corrected incoming prefactor
-- statement:
--   Work in the reduced, dispersionless conformal acoustic model with instantaneous quench and no backscattering. Let $V<0$, $a=|V|$, $c_{\rm in}>a$, $\kappa,n,\ell_\perp,m,\hbar,k_B>0$, and $n_1=n\ell_\perp^2$. The constant flow is $V$ and
--   $$c(x)=a\left(1+\frac23\tanh z(x)\right),\qquad z(x)=\frac{3\kappa x}{2a}.$$
--   The assertions are exact within this reduced model; they give no microscopic approximation error. No physical value of the discontinuous quench at $t=0$ is assigned.
--
--   Write $u_{\rm in}(t,x)=t-x/(c_{\rm in}-a)$, $v_{\rm in}(t,x)=t+x/(c_{\rm in}+a)$, and
--   $$u(t,x)=t-\frac{\log\sinh z(|x|)}\kappa,\qquad v(t,x)=t+\frac{9\kappa x/(2a)-\log\cosh(z(x)+\operatorname{artanh}(1/3))}{8\kappa}.$$
--   The outgoing coordinate has domain $x\ne0$. Shell evaluations mean the smooth coordinate formulas at $t=0$, for matching only.
--
--   Set $A=3\kappa(a-c_{\rm in})/(2a)<0$ and $B=3\kappa(c_{\rm in}+a)/(2a)>0$. For $s\in\{1,-1\}$ set
--   $$U_s(r)=\frac{s}{A}\log\left(\sqrt{1+e^{-2\kappa r}}+e^{-\kappa r}\right).$$
--   Let
--   $$W_{\rm print}(r)=\frac{4\kappa r}{B}+\frac{\log(1+\sqrt{1+2\sqrt2 e^{-8\kappa r}})}{2B},\quad C=\frac{\log(2\sqrt2)}{2B},\quad W(r)=W_{\rm print}(r)-C.$$
--   At a nonzero position, $s=\operatorname{sign}(x)$, $U(t,x)=U_s(u(t,x))$, and $W(t,x)=W(v(t,x))$. The subtraction of $C$ corrects the integration constant missing from printed (13); all differences and map derivatives are unchanged.
--
--   For a real off-null field kernel $K(t,x;t',x')$, define its equal-time density observable by (5):
--   $$\mathcal D_c[K](t;x,x')=\frac{n_1^2}{m^2c(x)^2c(x')^2}\sqrt{\frac{m^2c(x)c(x')}{n_1^2}}\left[(\partial_t+V\partial_x)(\partial_{t'}+V\partial_{x'})K\right]_{t'=t}.$$
--   Thus differentiation precedes equal times and the reduction factor lies outside the derivatives. Put $H=\hbar n_1/(4\pi m)$. The real logarithmic representative suffices for these off-null differentiated observables; no assertion about a Wightman distribution is made.
--
--   At fixed $x>0$ and $x'<0$, let $c=c(x)$, $c'=c(x')$,
--   $$r=\log\frac{\sinh z(x)}{\sinh z(|x'|)},\quad d=\frac{9(x-x')}{16a}-\frac{1}{8\kappa}\log\frac{2e^{z(x)}+e^{-z(x)}}{2e^{z(x')}+e^{-z(x')}}.$$
--   Write
--   $$L_u=\frac{H\kappa^2}{4\sqrt{cc'}(c-a)(c'-a)\cosh^2(r/2)},\qquad L_{v,0}=-\frac{H}{\sqrt{cc'}(c+a)(c'+a)d^2}.$$
--   These are signed contributions. In particular, both are negative on these opposite sides of the horizon.
--
--   Let $G_0$ be the density observable obtained from the vacuum logarithmic kernel by (5). Then, at these fixed opposite-side points,
--   $$\lim_{t\to+\infty}G_0(t;x,x')=L_u+L_{v,0},\qquad v(t,x)-v(t,x')=d>0\quad\text{for every real }t.$$
--   The product $(c+a)(c'+a)$ corrects the square-root product printed in the incoming term of (15): equation (14) leaves exactly these two factors after the advanced-map slope cancels. This is a pointwise limit with the full spatial envelope; no exact minimizer at $x=-x'$ or uniform-in-space convergence is asserted. Independent moderation of the correction is pending.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 3, (15)--(16)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF p. 3, (15)--(16): pointwise stationary vacuum limit.
SOURCE CORRECTION: (15) prints a square root around the product of the
advanced factors. Equation (14) instead gives the product itself, encoded in
lateVacuumV. Independent moderation of this correction is pending.
No exact finite-distance valley minimizer or uniform spatial limit is claimed. -/
theorem stationaryVacuumCorrelator (p : AcousticModel) (x xp : ℝ)
    (hx : 0 < x) (hxp : xp < 0) :
    Tendsto (fun t => vacuumDensity p t x xp) atTop
      (nhds (lateU p x xp + lateVacuumV p x xp)) ∧
    (∀ t : ℝ, v p t x - v p t xp = advancedDistance p x xp) ∧
    0 < advancedDistance p x xp := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
