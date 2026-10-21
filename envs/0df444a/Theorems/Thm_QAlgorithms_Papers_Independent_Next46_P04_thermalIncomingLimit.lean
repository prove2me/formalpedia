-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_thermalIncomingLimit
-- name    : QAlgorithms.Papers.Independent.Next46.P04.thermalIncomingLimit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:42:24.566466+00:00
-- url     : https://prove2.me/theorems/4bf3a147-eb7d-474c-aaa2-48cddb245bbf
-- title:
--   Persistent incoming thermal dependence and the full stationary limit
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
--   Fix a finite real $T>0$, representing initial phonon equilibrium in the comoving frame as in (17)--(19), with Doppler frequencies $\omega_u=\omega c_{\rm in}/(c_{\rm in}-a)$, $\omega_v=\omega c_{\rm in}/(c_{\rm in}+a)$ and occupation $N_{\omega_{u,v}}=(e^{\hbar\omega_{u,v}/(k_BT)}-1)^{-1}$ for $\omega>0$. Set
--   $$A_u=\frac{\pi k_BT(c_{\rm in}-a)}{\hbar c_{\rm in}},\qquad A_v=\frac{\pi k_BT(c_{\rm in}+a)}{\hbar c_{\rm in}}.$$
--   The thermal field kernel is
--   $$K_T=-\frac{\hbar}{4\pi}\left(\log\left|\frac{\sinh(A_u\Delta U)}{A_u}\right|+\log\left|\frac{\sinh(A_v\Delta W)}{A_v}\right|\right).$$
--   Define $G_T=\mathcal D_c[K_T]$, and define $G_{u,T}$ and $G_{v,T}$ by applying the same operator to the respective single-sector kernels. This is a specified equilibrium initial state, not a quantifier over arbitrary initial states. Temperature zero is treated by the vacuum kernel separately.
--
--   At fixed $x>0$ and $x'<0$, let $c=c(x)$, $c'=c(x')$,
--   $$r=\log\frac{\sinh z(x)}{\sinh z(|x'|)},\quad d=\frac{9(x-x')}{16a}-\frac{1}{8\kappa}\log\frac{2e^{z(x)}+e^{-z(x)}}{2e^{z(x')}+e^{-z(x')}}.$$
--   Write
--   $$L_u=\frac{H\kappa^2}{4\sqrt{cc'}(c-a)(c'-a)\cosh^2(r/2)},\qquad L_{v,0}=-\frac{H}{\sqrt{cc'}(c+a)(c'+a)d^2}.$$
--   These are signed contributions. In particular, both are negative on these opposite sides of the horizon.
--
--   For every fixed finite $T>0$ define
--   $$\beta=\frac{4\kappa}{B}A_v=\frac{8\pi k_BT a}{3\hbar c_{\rm in}},\qquad L_{v,T}=-\frac{H\beta^2}{\sqrt{cc'}(c+a)(c'+a)\sinh^2(\beta d)}.$$
--   Then at the fixed opposite-side points,
--   $$\lim_{t\to+\infty}G_{v,T}(t;x,x')=L_{v,T},\qquad \lim_{t\to+\infty}G_T(t;x,x')=L_u+L_{v,T}.$$
--   This specifies the surviving incoming temperature dependence. The signed term is negative; the source's contradictory assertion of positivity is deferred separately rather than incorporated into this limit.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 5, Incoming stationary regime following (20)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF p. 5, persistent incoming thermal dependence, read through (13),(20):
exact signed incoming and full stationary limits. The incoming term is negative;
the contradictory prose asserting positivity is deferred separately in HARD.md. -/
theorem thermalIncomingLimit (p : AcousticModel) (T x xp : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hxp : xp < 0) :
    incomingThermalScale p T = 8 * Real.pi * p.kB * T * a p / (3 * p.hbar * p.cin) ∧
    Tendsto (fun t => thermalVDensity p T t x xp) atTop
      (nhds (lateThermalV p T x xp)) ∧
    Tendsto (fun t => thermalDensityObservable p T t x xp) atTop
      (nhds (lateU p x xp + lateThermalV p T x xp)) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
