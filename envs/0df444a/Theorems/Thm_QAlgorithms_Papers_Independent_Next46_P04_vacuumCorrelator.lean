-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_vacuumCorrelator
-- name    : QAlgorithms.Papers.Independent.Next46.P04.vacuumCorrelator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:39:24.333129+00:00
-- url     : https://prove2.me/theorems/7688ee0f-5abe-4120-bb88-80a145307b86
-- title:
--   Explicit vacuum density correlator from the differentiated field kernel
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
--   For $t>0$, $x>0$, $x'<0$, take the initial vacuum kernel $K_0=-\hbar(\log|\Delta U|+\log|\Delta W|)/(4\pi)$ and $G_0=\mathcal D_c[K_0]$. Then
--   $$G_0(t;x,x')=-\frac{H}{\sqrt{cc'}}\left(\frac{F_u}{(\Delta U)^2}+\frac{F_v}{(\Delta W)^2}\right).$$
--   For $t<0$ and $x\ne x'$, use $c=c_{\rm in}$ and the initial coordinates in the same differential construction; the result is
--   $$G_{\rm in}=-\frac{H}{c_{\rm in}}\left(\frac1{(c_{\rm in}-a)^2(\Delta u_{\rm in})^2}+\frac1{(c_{\rm in}+a)^2(\Delta v_{\rm in})^2}\right).$$
--   Here the two initial differences are evaluated at equal time. The formula evaluates the observable defined by (5), rather than defining the observable by the answer.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 3, (14) and following sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF p. 3, (14) and the sentence following it: evaluation of (5) from
(8), with independent points differentiated before equal times. Domains are
post-quench cross-horizon points and, separately, pre-quench distinct points. -/
theorem vacuumCorrelator (p : AcousticModel) :
    (∀ t x xp : ℝ, 0 < t → 0 < x → xp < 0 →
      vacuumDensity p t x xp = -correlatorScale p / Real.sqrt (soundSpeed p x * soundSpeed p xp) *
        (uFactor p t x xp / (mappedU p t x - mappedU p t xp) ^ 2 +
         vFactor p t x xp / (mappedW p t x - mappedW p t xp) ^ 2)) ∧
    (∀ t x xp : ℝ, t < 0 → x ≠ xp →
      initialDensity p t x xp = -correlatorScale p / p.cin *
        (1 / ((p.cin - a p) ^ 2 * (initialU p t x - initialU p t xp) ^ 2) +
         1 / ((p.cin + a p) ^ 2 * (initialW p t x - initialW p t xp) ^ 2))) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
