-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_qutritExample
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.qutritExample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:06:56.067733+00:00
-- url     : https://prove2.me/theorems/8ec3981f-f922-4149-81f7-ce583dc07284
-- title:
--   §2, qutrit symmetry saturation and multiplicativity
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   Set $d=3$ and let $\Phi\in W_1(H)$. If $|\phi(z)|=|\phi(-z)|$ for every $z$, then
--
--   $$\nu_2(\Phi)=S(\phi).$$
--
--   If also $|\phi(z)|\le1$ for every $z$, then $\nu_2(\Phi\otimes\Omega)=\nu_2(\Phi)\nu_2(\Omega)$ for every finite-dimensional CP partner $\Omega$. Hermiticity preservation, meaning that Hermitian inputs have Hermitian outputs, implies the required modulus symmetry.
--
--   This is the extension from qutrit channels to normalized maps with symmetric symbol moduli. Hermiticity preservation is not self-adjointness of the superoperator.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 7, §2, qutrit symmetry saturation and multiplicativity

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

/-- Section 2, PDF p.7: qutrit modulus symmetry gives saturation; (2.6) is
retained for multiplicativity. Hermiticity preserving maps supply the symmetry. -/
theorem qutritExample (Phi : Op (ZMod 3) →ₗ[ℂ] Op (ZMod 3)) (hPhi : NormalizedWeylMap Phi) :
    ((∀ z, ‖symbol Phi z‖ = ‖symbol Phi (-z)‖) →
      nu 2 Phi = saturationValue (symbol Phi) ∧
      ((∀ z, ‖symbol Phi z‖ ≤ 1) → UniversalMultiplicative 2 Phi)) ∧
    (HermiticityPreserving Phi → ∀ z, ‖symbol Phi z‖ = ‖symbol Phi (-z)‖) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
