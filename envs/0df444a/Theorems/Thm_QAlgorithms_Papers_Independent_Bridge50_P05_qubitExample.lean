-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_qubitExample
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.qubitExample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:07:38.617688+00:00
-- url     : https://prove2.me/theorems/67fb73f6-cdd6-4e33-8ff1-7096d80a2fa3
-- title:
--   §2, arbitrary normalized qubit maps and unital qubit channels
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   Set $d=2$. Every $\Phi\in W_1(H)$ satisfies
--
--   $$\nu_2(\Phi)=S(\phi).$$
--
--   When $|\phi(z)|\le1$ for all $z$, multiplicativity holds with every finite-dimensional CP partner. In addition, every unital qubit channel, regardless of whether it is diagonal in the specified fixed Pauli coordinates, has this multiplicativity property.
--
--   This includes arbitrary normalized qubit Weyl maps for saturation and all unital qubit channels for multiplicativity; independent input/output unitaries are permitted in the latter normal form.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 7, §2, arbitrary normalized qubit maps and unital qubit channels

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

/-- Section 2, PDF pp.7--8: all normalized qubit maps saturate; contractivity
implies multiplicativity. Arbitrary unital qubit channels are included independently
of their fixed-coordinate Pauli form (pre/post unitaries need not agree). -/
theorem qubitExample :
    (∀ Phi : Op (ZMod 2) →ₗ[ℂ] Op (ZMod 2), NormalizedWeylMap Phi →
      nu 2 Phi = saturationValue (symbol Phi) ∧
      ((∀ z, ‖symbol Phi z‖ ≤ 1) → UniversalMultiplicative 2 Phi)) ∧
    (∀ Phi : Op (ZMod 2) →ₗ[ℂ] Op (ZMod 2), IsChannel Phi → Phi 1 = 1 →
      UniversalMultiplicative 2 Phi) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
