-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_weylRepresentation
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.weylRepresentation
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:04:19.674022+00:00
-- url     : https://prove2.me/theorems/5eefd863-4d58-4fcc-927d-df1539b2630a
-- title:
--   §2, diagonalization, Fourier mixture and convolution
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   For an additive subgroup $G\le Z$, let $J(x,y)=(y,-x)$, $\chi(\gamma,z)=\exp(2\pi i(\gamma_xz_x+\gamma_yz_y)/d)$, and $G^\perp=\{\gamma:\chi(\gamma,z)=1\text{ for every }z\in G\}$. The symbol $\phi_{G,a,b}$ is $1$ at zero, $a+b$ on $G\setminus\{0\}$, and $b$ off $G$. Define $\Psi_G(X)=d^{-1}\sum_{z\in G^\perp}W_{Jz}XW_{Jz}^*$ and $\Phi_{G,a,b}(X)=a\Psi_G(X)+bX+(1-a-b)\operatorname{Tr}(X)I/d$.
--
--   For any Weyl-covariant complex-linear maps $\Phi,\Theta$, without assuming normalization, define $p^\Phi_\gamma=d^{-2}\sum_z\phi(z)\chi(\gamma,z)$. Then
--
--   $$\Phi(W_z)=\phi(z)W_z,\quad \Phi(X)=\sum_z f_X(z)\phi(z)W_z=\sum_\gamma p^\Phi_\gamma W_{J\gamma}XW_{J\gamma}^*,\quad\phi(z)=\sum_\gamma p^\Phi_\gamma\chi(\gamma,-z).$$
--
--   The maps commute. The symbol of their composition is the pointwise product, and its Fourier coefficients are the convolution $p_\gamma=\sum_\eta p^\Phi_\eta p^\Theta_{\gamma-\eta}$; the same mixture formula holds for the composition. Conversely, the finite formula $\Phi_\phi(X)=\sum_z f_X(z)\phi(z)W_z$ has Weyl eigenvalues $\phi(z)$ and is Weyl covariant for every complex symbol $\phi$.
--
--   This identifies the diagonal, Fourier-mixture and convolution descriptions of arbitrary Weyl-covariant linear maps. No claim that every map can be rescaled to $\phi(0)=1$ is made.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 3, §2, diagonalization, Fourier mixture and convolution

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

/-- Section 2, PDF pp.3--4, (2.1)--(2.2): unnormalized covariant linear maps
are diagonal, have the Fourier mixture, and compose by symbol product/weylConvolution.
No claim that a zero symbol at zero can be rescaled to one. -/
theorem weylRepresentation (Phi Psi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d))
    (hPhi : WeylCovariantMap Phi) (hPsi : WeylCovariantMap Psi) :
    (∀ z, Phi (W z) = symbol Phi z • W z) ∧
    (∀ X, Phi X = multiplier (symbol Phi) X) ∧
    (∀ z, symbol Phi z = ∑ g, fourier (symbol Phi) g * duality g (-z)) ∧
    (∀ X, Phi X = ∑ g, fourier (symbol Phi) g • (W (rotateWeylLabel g) * X * (W (rotateWeylLabel g))ᴴ)) ∧
    (∀ X, Phi (Psi X) = Psi (Phi X)) ∧
    (∀ z, symbol (fun X => Phi (Psi X)) z = symbol Phi z * symbol Psi z) ∧
    (∀ g, fourier (symbol (fun X => Phi (Psi X))) g =
      weylConvolution (fourier (symbol Phi)) (fourier (symbol Psi)) g) ∧
    (∀ X, Phi (Psi X) = ∑ g,
      weylConvolution (fourier (symbol Phi)) (fourier (symbol Psi)) g •
        (W (rotateWeylLabel g) * X * (W (rotateWeylLabel g))ᴴ)) ∧
    (∀ phi : WeylLabel d → ℂ,
      (∀ z, multiplier phi (W z) = phi z • W z) ∧
      (∀ z X, multiplier phi (W z * X * (W z)ᴴ) =
        W z * multiplier phi X * (W z)ᴴ)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
