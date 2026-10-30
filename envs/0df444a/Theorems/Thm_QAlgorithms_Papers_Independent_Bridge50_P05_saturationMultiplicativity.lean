-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_saturationMultiplicativity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.saturationMultiplicativity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:59:55.096845+00:00
-- url     : https://prove2.me/theorems/0f5120d7-ce55-456a-bffc-1343b4e2e967
-- title:
--   Theorem 2, saturation implies multiplicativity
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   Let $\Phi\in W_1(H)$. If $|\phi(z)|\le1$ for every $z\in Z$ and $\nu_2(\Phi)=S(\phi)$, then, for every completely positive map $\Omega$ between finite-dimensional matrix algebras with nonzero input dimension,
--
--   $$\nu_2(\Phi\otimes\Omega)=\nu_2(\Phi)\nu_2(\Omega).$$
--
--   The partner need not preserve trace. This turns saturation of the principal bound into multiplicativity.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 5, Theorem 2, saturation implies multiplicativity

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

/-- Theorem 2, PDF pp.5--6: saturation and (2.6) imply multiplicativity
with EVERY finite-dimensional CP partner, including non-TP partners. -/
theorem saturationMultiplicativity (Phi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d))
    (hPhi : NormalizedWeylMap Phi) (hbound : ∀ z, ‖symbol Phi z‖ ≤ 1)
    (hsat : nu 2 Phi = saturationValue (symbol Phi)) :
    UniversalMultiplicative 2 Phi := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
