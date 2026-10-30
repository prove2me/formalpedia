-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_complementaryBlockConstruction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.complementaryBlockConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:13:10.140574+00:00
-- url     : https://prove2.me/theorems/9f49d3c0-0ce4-4109-af72-d6e09b8c7c75
-- title:
--   §3, explicit complementary Weyl-channel block construction
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   Let $\lambda:Z\to[0,\infty)$ satisfy $\sum_{x,y}\lambda_{x,y}^2=1$. Write indices cyclically as $1,\ldots,d$, with $d$ representing residue zero. Reorder the actual Kraus family as $K_{s,r}=\lambda_{1-r,1-s}W_{(1-r,1-s)}$. Define
--
--   $$D_s=\operatorname{diag}_r(\lambda_{1-r,1-s}),\qquad\widetilde W_{(s,r),(t,u)}=(D_sU^{1-t}V^{1-s})_{r,u}.$$
--
--   Then $\Phi(X)=\sum_{s,r}K_{s,r}XK_{s,r}^*$ is a channel. Its complementary Kraus rows satisfy $\widetilde K_t((s,r),u)=K_{s,r}(t,u)=(D_sU^{1-t}V^{1-s})_{r,u}$. For the same dilation $A_{(t,(s,r)),u}=K_{s,r}(t,u)$, define the complementary map independently by tracing out the output $H$. On every operator,
--
--   $$\widetilde\Phi(X)=\operatorname{Tr}_H(AXA^*)=\widetilde W(I_d\otimes X)\widetilde W^*.$$
--
--   Here $\widetilde W$ is $d^2\times d^2$ and each $\widetilde K_t$ is $d^2\times d$. This is the explicit block construction for the actual complementary channel, with a canonical nonnegative Kraus-amplitude choice.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 10, §3, explicit complementary Weyl-channel block construction

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P05

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P34 (cyclicPhase weyl dephasing)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (nu superopTensor UniversalMultiplicative rowKraus indexedKrausDilation)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ} [NeZero d]

/-- Section 3, PDF pp.11--13: explicit complementary Weyl-channel blocks.
The target complement is independently computed from the same actual Kraus dilation;
I in I tensor X has dimension d and Wtilde has dimension d². -/
theorem complementaryBlockConstruction (lam : WeylLabel d → ℝ)
    (hlam : ∀ z, 0 ≤ lam z) (hnorm : ∑ z, lam z ^ 2 = 1) :
    IsChannel (krausApply (reorderedKraus lam)) ∧
    (∀ t : ZMod d, rowKraus (reorderedKraus lam) t =
      fun sr u =>
        let M : Op (ZMod d) := diagonalBlock lam sr.1 * W (1 - t, 1 - sr.1)
        M sr.2 u) ∧
    (∀ X : Op (ZMod d),
      complementaryChannel (indexedKrausDilation (reorderedKraus lam)) X =
        complementBlock lam * ((1 : Op (ZMod d)) ⊗ₖ X) * (complementBlock lam)ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
