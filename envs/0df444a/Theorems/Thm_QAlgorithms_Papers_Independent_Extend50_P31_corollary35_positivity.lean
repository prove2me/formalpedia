-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary35_positivity
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary35_positivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:46:40.688086+00:00
-- url     : https://prove2.me/theorems/0c4c8bcd-febc-4ae1-9233-21327d032be9
-- title:
--   Corollary 35: complete positivity through explicit Choi eigenvalues
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For $\Phi_l=\sum_\Theta l_\alpha P_\alpha$ with $l_{\mathrm{id}}=1$, put $\epsilon_i^\beta=\sum_\alpha l_\alpha\mu_i(\alpha,\beta)$. The common vectors are eigenvectors of $J(\Phi_l)$ with these eigenvalues, and
--
--   $$
--   \epsilon_i^\beta=\frac1{|G|}\sum_g\left(\sum_\alpha l_\alpha d_\alpha\chi_\alpha(g^{-1})\right)|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2,\qquad J(\Phi_l)\succeq0\ \Longleftrightarrow\ \forall\beta,i,\ \epsilon_i^\beta\in\mathbb R_{\ge0}.
--   $$
--
--   This describes the complete positivity through explicit Choi eigenvalues in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 16, Corollary 35: complete positivity through explicit Choi eigenvalues

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

/-- PDF p.16, Corollary 35 Eq.(80), including the spectral equation and full complex reality. -/
theorem corollary35_positivity (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ)
    (hl : trivialCoefficient D l = 1) :
    (∀ r, (choi (spectralMap D l)).mulVec (choiVector D P r) =
      choiEigenvalueVector D P l r • choiVector D P r) ∧
    ((choi (spectralMap D l)).PosSemidef ↔ ∀ r, NonnegativeScalar (choiEigenvalueVector D P l r)) ∧
    (∀ r, choiEigenvalueVector D P l r = (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
      (∑ a : OccurringIrrep D, l a * (D.F.dim a.val : ℂ) * character (D.F.irrep a.val) g⁻¹) *
        (Complex.normSq (Matrix.trace (eigenmatrix D P r * (D.U.rho g)ᴴ)) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
