-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_thermalCorrelator
-- name    : QAlgorithms.Papers.Independent.Next46.P04.thermalCorrelator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:40:52.140991+00:00
-- url     : https://prove2.me/theorems/500a2492-27cf-4593-b069-012688223caa
-- title:
--   Explicit density correlator for initial thermal equilibrium
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
--   Use primes on $U_s$ and $W$ for derivatives with respect to their scalar null argument. Put $c=c(x)$, $c'=c(x')$, $\Delta U=U(t,x)-U(t,x')$, $\Delta W=W(t,x)-W(t,x')$, and
--   $$F_u=\frac{U_s'(u(t,x))U_{s'}'(u(t,x'))}{(c-a)(c'-a)},\qquad F_v=\frac{W'(v(t,x))W'(v(t,x'))}{(c+a)(c'+a)},$$
--   where $s=\operatorname{sign}(x)$ and $s'=\operatorname{sign}(x')$.
--
--   Fix a finite real $T>0$, representing initial phonon equilibrium in the comoving frame as in (17)--(19), with Doppler frequencies $\omega_u=\omega c_{\rm in}/(c_{\rm in}-a)$, $\omega_v=\omega c_{\rm in}/(c_{\rm in}+a)$ and occupation $N_{\omega_{u,v}}=(e^{\hbar\omega_{u,v}/(k_BT)}-1)^{-1}$ for $\omega>0$. Set
--   $$A_u=\frac{\pi k_BT(c_{\rm in}-a)}{\hbar c_{\rm in}},\qquad A_v=\frac{\pi k_BT(c_{\rm in}+a)}{\hbar c_{\rm in}}.$$
--   The thermal field kernel is
--   $$K_T=-\frac{\hbar}{4\pi}\left(\log\left|\frac{\sinh(A_u\Delta U)}{A_u}\right|+\log\left|\frac{\sinh(A_v\Delta W)}{A_v}\right|\right).$$
--   Define $G_T=\mathcal D_c[K_T]$, and define $G_{u,T}$ and $G_{v,T}$ by applying the same operator to the respective single-sector kernels. This is a specified equilibrium initial state, not a quantifier over arbitrary initial states. Temperature zero is treated by the vacuum kernel separately.
--
--   For $t>0$, $x>0$, and $x'<0$,
--   $$G_T(t;x,x')=-\frac{H}{\sqrt{cc'}}\left(F_u\frac{A_u^2}{\sinh^2(A_u\Delta U)}+F_v\frac{A_v^2}{\sinh^2(A_v\Delta W)}\right).$$
--   This evaluates the density observable of the thermal field kernel. It does not construct a new Gibbs state or extend the displayed positive-temperature quotients to $T=0$.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 4, (19)--(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF p. 4, (20): evaluation of (5) using the fixed initial thermal kernel
(19). Temperature is strictly positive; the vacuum is a separate observable. -/
theorem thermalCorrelator (p : AcousticModel) (T t x xp : ℝ)
    (hT : 0 < T) (ht : 0 < t) (hx : 0 < x) (hxp : xp < 0) :
    thermalDensityObservable p T t x xp =
      -correlatorScale p / Real.sqrt (soundSpeed p x * soundSpeed p xp) *
        (uFactor p t x xp * (Au p T) ^ 2 /
          (Real.sinh (Au p T * (mappedU p t x - mappedU p t xp))) ^ 2 +
         vFactor p t x xp * (Av p T) ^ 2 /
          (Real.sinh (Av p T * (mappedW p t x - mappedW p t xp))) ^ 2) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
