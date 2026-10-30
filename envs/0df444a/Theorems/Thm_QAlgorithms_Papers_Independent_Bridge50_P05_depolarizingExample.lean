-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_depolarizingExample
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.depolarizingExample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:08:27.828402+00:00
-- url     : https://prove2.me/theorems/4bdbef4f-5147-4730-9e20-bf3e268c9787
-- title:
--   §2, complex depolarizing multiplier example
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   Let $\lambda\in\mathbb C$ with $|\lambda|\le1$ and define $D_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. This map commutes with conjugation by every unitary, has symbol $1$ at zero and $\lambda$ elsewhere, and
--
--   $$E_{\max}=Z\setminus\{0\},\qquad\nu_2(D_\lambda)=S(\phi_{D_\lambda}),\qquad\nu_2(D_\lambda\otimes\Omega)=\nu_2(D_\lambda)\nu_2(\Omega)$$
--
--   for every finite-dimensional CP partner $\Omega$. For $d=1$ the map is the identity and $E_{\max}$ is empty. This example explicitly allows complex parameters for which the map is not a channel.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 8, §2, complex depolarizing multiplier example

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

/-- Section 2, PDF p.8: arbitrary complex depolarizing parameters of modulus
at most one; no channel hypothesis. At d=1 the map is the identity. -/
theorem depolarizingExample (lam : ℂ) (hlam : ‖lam‖ ≤ 1) :
    (∀ U : Matrix.unitaryGroup (ZMod d) ℂ, ∀ X,
      complexDepolarizing (d := d) lam ((U : Op (ZMod d)) * X * (U : Op (ZMod d))ᴴ) =
        (U : Op (ZMod d)) * complexDepolarizing (d := d) lam X * (U : Op (ZMod d))ᴴ) ∧
    (∀ z : WeylLabel d, symbol (complexDepolarizing (d := d) lam) z = if z = 0 then 1 else lam) ∧
    optimizers (symbol (complexDepolarizing (d := d) lam)) = {z : WeylLabel d | z ≠ 0} ∧
    nu 2 (complexDepolarizing (d := d) lam) = saturationValue (symbol (complexDepolarizing (d := d) lam)) ∧
    UniversalMultiplicative 2 (complexDepolarizing (d := d) lam) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
