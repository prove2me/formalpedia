-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_stateFourier
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.stateFourier
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:03:15.809058+00:00
-- url     : https://prove2.me/theorems/88bb6725-697b-4286-ba18-173e2091f083
-- title:
--   §1, density-state Fourier bounds and purity characterization
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   For every density matrix $\rho\ge0$ of trace one,
--
--   $$f_\rho(0)=\frac1d,\qquad |f_\rho(z)|\le\frac1d\quad(z\in Z),\qquad\sum_{z\ne0}|f_\rho(z)|^2\le\frac{d-1}{d^2}.$$
--
--   Moreover,
--
--   $$\rho\text{ is a unit-vector pure state}\ \Longleftrightarrow\ \operatorname{Tr}(\rho^2)=1\ \Longleftrightarrow\ \sum_{z\ne0}|f_\rho(z)|^2=\frac{d-1}{d^2}.$$
--
--   These bounds characterize purity through the nonidentity Fourier mass. For $d=1$ that mass is zero.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 3, §1, density-state Fourier bounds and purity characterization

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

/-- Section 1, PDF p.3, (1.8)--(1.9): normalized density inputs and both
purity equivalences. Dimension subtraction in the mass bound is real. -/
theorem stateFourier (rho : Op (ZMod d)) (hrho : IsDensityMatrix rho) :
    weylFourierCoefficient rho 0 = (d : ℂ)⁻¹ ∧
    (∀ z, ‖weylFourierCoefficient rho z‖ ≤ (d : ℝ)⁻¹) ∧
    (∑ z ∈ Finset.univ.filter (fun z : WeylLabel d => z ≠ 0), ‖weylFourierCoefficient rho z‖ ^ 2) ≤
      ((d : ℝ) - 1) / (d : ℝ) ^ 2 ∧
    (IsPure rho ↔ (rho * rho).trace = 1) ∧
    (IsPure rho ↔
      (∑ z ∈ Finset.univ.filter (fun z : WeylLabel d => z ≠ 0), ‖weylFourierCoefficient rho z‖ ^ 2) =
        ((d : ℝ) - 1) / (d : ℝ) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
