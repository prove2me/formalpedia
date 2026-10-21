-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_signedShellMatching
-- name    : QAlgorithms.Papers.Independent.Next46.P04.signedShellMatching
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:38:45.091003+00:00
-- url     : https://prove2.me/theorems/c66bc5eb-ae03-4623-a0c9-85a3ddcabca6
-- title:
--   Signed shell inverses with corrected advanced constant
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
--   Define the actual shell maps $S_u(y)=u(0,-(c_{\rm in}-a)y)$ and $S_v(y)=v(0,(c_{\rm in}+a)y)$. Then
--   $$S_u(U_s(r))=r,\qquad-\kappa r=\log\sinh|AU_s(r)|,\qquad S_v(W(r))=r.$$
--   Moreover $U_1(r)<0<U_{-1}(r)$, and at the shell
--   $$U(0,x)=u_{\rm in}(0,x)\ (x\ne0),\qquad W(0,x)=v_{\rm in}(0,x),\qquad W_{\rm print}(v(0,x))=v_{\rm in}(0,x)+C.$$
--   This retains the opposite retarded branches and states inverseness for the constructed shell maps, rather than assuming it. The additive correction requires independent moderation.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 3, (11)--(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF pp. 2--3, (11)--(13): signed inverses of the actual shell maps.
SOURCE CORRECTION: printed (13) lacks -log(2 sqrt(2))/(2B). With (10)'s
constant it gives initialW + advancedOffset on the shell, not initialW.
The corrected advancedIn and the printed offset identity are both retained.
Independent moderation of this correction is pending. -/
theorem signedShellMatching (p : AcousticModel) :
    A p < 0 ∧ 0 < B p ∧
    (∀ s : ℝ, s = 1 ∨ s = -1 → ∀ r : ℝ,
      retardedShell p (retardedIn p s r) = r ∧
      -p.kappa * r = Real.log (Real.sinh |A p * retardedIn p s r|) ∧
      (s = 1 → retardedIn p s r < 0) ∧
      (s = -1 → 0 < retardedIn p s r)) ∧
    (∀ x : ℝ, x ≠ 0 → mappedU p 0 x = initialU p 0 x) ∧
    (∀ r : ℝ, advancedShell p (advancedIn p r) = r) ∧
    (∀ x : ℝ, mappedW p 0 x = initialW p 0 x ∧
      advancedPrinted p (v p 0 x) = initialW p 0 x + advancedOffset p) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
