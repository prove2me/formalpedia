-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_twoParameterFormula
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.twoParameterFormula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:09:14.026933+00:00
-- url     : https://prove2.me/theorems/fef2146a-2c89-4bc5-8703-4d96b5bad2d7
-- title:
--   §2, subgroup two-parameter Fourier and twirl formulae (2.13)–(2.19)
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   For an additive subgroup $G\le Z$, let $J(x,y)=(y,-x)$, $\chi(\gamma,z)=\exp(2\pi i(\gamma_xz_x+\gamma_yz_y)/d)$, and $G^\perp=\{\gamma:\chi(\gamma,z)=1\text{ for every }z\in G\}$. The symbol $\phi_{G,a,b}$ is $1$ at zero, $a+b$ on $G\setminus\{0\}$, and $b$ off $G$. Define $\Psi_G(X)=d^{-1}\sum_{z\in G^\perp}W_{Jz}XW_{Jz}^*$ and $\Phi_{G,a,b}(X)=a\Psi_G(X)+bX+(1-a-b)\operatorname{Tr}(X)I/d$.
--
--   Assume $|G|=d$ and let $a,b\in\mathbb C$. The Fourier coefficients are
--
--   $$p_\gamma=\frac1{d^2}\begin{cases}1+a(d-1)+b(d^2-1),&\gamma=0,\\1+a(d-1)-b,&\gamma\in G^\perp\setminus\{0\},\\1-a-b,&\gamma\notin G^\perp.\end{cases}$$
--
--   For every subgroup $\Gamma\le Z$, character orthogonality reads $\sum_{z\in\Gamma}\chi(\gamma,z)=|\Gamma|$ if $\gamma\in\Gamma^\perp$, and zero otherwise. The Weyl multiplier with symbol $\phi_{G,a,b}$ equals $\Phi_{G,a,b}$ on all operators. If $G$ is maximal degenerate, then
--
--   $$G^\perp=JG,\qquad\Psi_G(X)=\frac1d\sum_{z\in G}W_zXW_z^*.$$
--
--   These formulas provide the two-parameter family directly from its Fourier symbol and fix the twirl over the correct annihilator.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 8, §2, subgroup two-parameter Fourier and twirl formulae (2.13)–(2.19)

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

/-- Section 2, PDF pp.8--9, (2.13)--(2.19): finite Fourier coefficients,
character orthogonality, the annihilator twirl, and its maximal-degenerate form.
The malformed real exponential in printed (2.16) is not used. -/
theorem twoParameterFormula (G : AddSubgroup (WeylLabel d))
    (hcard : (G : Set (WeylLabel d)).ncard = d) (a b : ℂ) :
    (∀ g, fourier (twoSymbol G a b) g = (d : ℂ)⁻¹ ^ 2 *
      (if g = 0 then 1 + a * ((d : ℂ) - 1) + b * ((d : ℂ) ^ 2 - 1)
       else if g ∈ annihilator G then 1 + a * ((d : ℂ) - 1) - b
       else 1 - a - b)) ∧
    (∀ Gamma : AddSubgroup (WeylLabel d), ∀ g,
      (∑ z ∈ Finset.univ.filter (fun z => z ∈ Gamma), duality g z) =
        if g ∈ annihilator Gamma then ((Gamma : Set (WeylLabel d)).ncard : ℂ) else 0) ∧
    (∀ X, multiplier (twoSymbol G a b) X = twoMap G a b X) ∧
    (MaximalDegenerate G →
      annihilator G = rotateWeylLabel '' (G : Set (WeylLabel d)) ∧
      ∀ X, subgroupTwirl G X = (d : ℂ)⁻¹ •
        ∑ z ∈ Finset.univ.filter (fun z => z ∈ G), W z * X * (W z)ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
