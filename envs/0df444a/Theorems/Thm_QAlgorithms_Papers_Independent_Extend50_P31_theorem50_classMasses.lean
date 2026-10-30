-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_theorem50_classMasses
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.theorem50_classMasses
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:54:53.926364+00:00
-- url     : https://prove2.me/theorems/ffe622fe-cd7b-47f3-8924-6742e44d3da4
-- title:
--   Theorem 50: channels from nonnegative conjugacy-class masses
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Let $f:G\to\mathbb C$ satisfy $\sum_g f(g)=|G|$ and require that each conjugacy-class sum $\sum_{h\in K}f(h)$ be real and nonnegative. Define
--
--   $$
--   l_\alpha=\frac1{|G|d_\alpha}\sum_g\chi_\alpha(g)f(g),\qquad\Phi_f=\sum_{\alpha\in\Theta}l_\alpha P_\alpha.\qquad\Phi_f\text{ is an ICQC and }l_{\mathrm{id}}=1.
--   $$
--
--   This describes the channels from nonnegative conjugacy-class masses in the fixed source conventions.
--
--   **Formalization Note** The trivial coefficient is extracted by summing the coefficient at the trivial label, without assuming in the input data the theorem that this label occurs.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 21, Theorem 50: channels from nonnegative conjugacy-class masses

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.21, Theorem 50 Eqs.(107)--(109), proof p.23 Eq.(120).
The hypothesis is nonnegative class masses, not pointwise nonnegativity of complex f. -/
theorem theorem50_classMasses (D : Data G A n) (f : G → ℂ)
    (hsum : ∑ g, f g = (Fintype.card G : ℂ))
    (hclass : ∀ g, NonnegativeScalar (∑ h ∈ conjugacyClass g, f h)) :
    IsIrrepCovariant D.U (spectralMap D (classCoefficients D f)) ∧
    IsPaperChannel (spectralMap D (classCoefficients D f)) ∧
    trivialCoefficient D (classCoefficients D f) = 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
