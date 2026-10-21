-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_lateNullAsymptotics
-- name    : QAlgorithms.Papers.Independent.Next46.P04.lateNullAsymptotics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:39:45.770507+00:00
-- url     : https://prove2.me/theorems/2113c9cb-9d8b-4719-a979-1d23f1de7a92
-- title:
--   Late outgoing and incoming ratio asymptotics
-- statement:
--   Work in the reduced, dispersionless conformal acoustic model with instantaneous quench and no backscattering. Let $V<0$, $a=|V|$, $c_{\rm in}>a$, $\kappa,n,\ell_\perp,m,\hbar,k_B>0$, and $n_1=n\ell_\perp^2$. The constant flow is $V$ and
--   $$c(x)=a\left(1+\frac23\tanh z(x)\right),\qquad z(x)=\frac{3\kappa x}{2a}.$$
--   The assertions are exact within this reduced model; they give no microscopic approximation error. No physical value of the discontinuous quench at $t=0$ is assigned.
--
--   Set $A=3\kappa(a-c_{\rm in})/(2a)<0$ and $B=3\kappa(c_{\rm in}+a)/(2a)>0$. For $s\in\{1,-1\}$ set
--   $$U_s(r)=\frac{s}{A}\log\left(\sqrt{1+e^{-2\kappa r}}+e^{-\kappa r}\right).$$
--   Let
--   $$W_{\rm print}(r)=\frac{4\kappa r}{B}+\frac{\log(1+\sqrt{1+2\sqrt2 e^{-8\kappa r}})}{2B},\quad C=\frac{\log(2\sqrt2)}{2B},\quad W(r)=W_{\rm print}(r)-C.$$
--   At a nonzero position, $s=\operatorname{sign}(x)$, $U(t,x)=U_s(u(t,x))$, and $W(t,x)=W(v(t,x))$. The subtraction of $C$ corrects the integration constant missing from printed (13); all differences and map derivatives are unchanged.
--
--   For each fixed branch $s\in\{1,-1\}$,
--   $$\lim_{r\to+\infty}\frac{|AU_s(r)|}{e^{-\kappa r}}=1,\qquad \lim_{r\to+\infty}\frac{W(r)}{4\kappa r/B}=1.$$
--   These ratios specify the asymptotic equivalences used in the stationary correlator. The absolute value here does not erase the signed branches from the correlator.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 3, Text immediately before (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF p. 3, text immediately before (15): ratio asymptotics on each fixed
signed outgoing branch and for the incoming map. Additive correction to (13)
does not affect its ratio limit. -/
theorem lateNullAsymptotics (p : AcousticModel) :
    (∀ s : ℝ, s = 1 ∨ s = -1 →
      Tendsto (fun r => |A p * retardedIn p s r| / Real.exp (-p.kappa * r))
        atTop (nhds 1)) ∧
    Tendsto (fun r => advancedIn p r / (4 * p.kappa * r / B p)) atTop (nhds 1) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
