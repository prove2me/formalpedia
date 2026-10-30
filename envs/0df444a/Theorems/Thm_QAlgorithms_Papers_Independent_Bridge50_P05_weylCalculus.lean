-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_weylCalculus
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.weylCalculus
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:02:24.604164+00:00
-- url     : https://prove2.me/theorems/329e7ca9-14c7-475d-90c5-b83b5f8d782c
-- title:
--   §1, Weyl relations and Fourier inversion/Parseval
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   For every operator $X$ and all $z=(x,y),v=(x',y')\in Z$, the positive-clock Weyl calculus gives
--
--   $$W_zW_v=e^{2\pi i yx'/d}W_{z+v}=e^{2\pi i(x'y-y'x)/d}W_vW_z,\qquad W_z^*=e^{2\pi i yx/d}W_{-z},$$
--   $$\operatorname{Tr}(W_zW_v^*)=d\,\delta_{zv},\qquad X=\sum_z f_X(z)W_z,$$
--   $$\operatorname{Tr}X=df_X(0),\qquad \operatorname{Tr}(X^*X)=d\sum_z|f_X(z)|^2,$$
--   $$\overline{f_X(z)}=e^{-2\pi i yx/d}f_{X^*}(-z).$$
--
--   Thus the Weyl operators are an orthogonal operator basis with the displayed inversion and Parseval formulas. All phase arithmetic is understood modulo $d$.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 2, §1, Weyl relations and Fourier inversion/Parseval

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

/-- Section 1, PDF pp.2--3, (1.3)--(1.7),(1.10): positive-clock Weyl
relations, trace orthogonality, inversion, Parseval and the conjugated adjoint relation. -/
theorem weylCalculus (X : Op (ZMod d)) :
    (∀ z v : WeylLabel d, W z * W v = cyclicPhase d (z.2 * v.1) • W (z + v)) ∧
    (∀ z v : WeylLabel d, W z * W v =
      cyclicPhase d (v.1 * z.2 - v.2 * z.1) • (W v * W z)) ∧
    (∀ z : WeylLabel d, (W z)ᴴ = cyclicPhase d (z.2 * z.1) • W (-z)) ∧
    (∀ z v : WeylLabel d, (W z * (W v)ᴴ).trace = if z = v then (d : ℂ) else 0) ∧
    X = ∑ z, weylFourierCoefficient X z • W z ∧
    X.trace = (d : ℂ) * weylFourierCoefficient X 0 ∧
    (Xᴴ * X).trace = (((d : ℝ) * ∑ z, ‖weylFourierCoefficient X z‖ ^ 2 : ℝ) : ℂ) ∧
    (∀ z : WeylLabel d, conj (weylFourierCoefficient X z) =
      cyclicPhase d (-(z.2 * z.1)) * weylFourierCoefficient Xᴴ (-z)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
