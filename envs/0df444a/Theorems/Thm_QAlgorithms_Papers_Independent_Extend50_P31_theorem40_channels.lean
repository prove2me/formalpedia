-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_theorem40_channels
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.theorem40_channels
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:49:43.409398+00:00
-- url     : https://prove2.me/theorems/8d56400c-1505-4197-906a-ae6fd03258da
-- title:
--   Theorem 40: characterization of all irreducibly covariant quantum channels
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For a complex-linear map $\Phi$, covariance, complete positivity and trace preservation are equivalent to a character-projector expansion satisfying the explicit scalar inequalities. Define $c_l(g)=\sum_\alpha l_\alpha d_\alpha\chi_\alpha(g^{-1})$. Then
--
--   $$
--   \Phi\text{ is an ICQC}\ \Longleftrightarrow\ \exists l:\Theta\to\mathbb C:\ \Phi=\sum_\alpha l_\alpha P_\alpha,\quad l_{\mathrm{id}}=1,\quad\sum_g c_l(g)|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2\in\mathbb R_{\ge0}\quad\forall\beta,i.
--   $$
--
--   Each occurring projector has nonzero range, and $\Phi(P_\alpha X)=l_\alpha P_\alpha X$ for all $X$. This is the full two-direction characterization, with no real-character restriction.
--
--   **Formalization Note** The trivial coefficient is extracted by summing the coefficient at the trivial label, without assuming in the input data the theorem that this label occurs.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 17, Theorem 40: characterization of all irreducibly covariant quantum channels

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

/-- PDF p.17, Theorem 40 Eqs.(88),(89), preserving the original topic seed.
Both directions characterize covariance, complete positivity and trace preservation. -/
theorem theorem40_channels (D : Data G A n) (P : Pivots D) (Phi : EndMat n) :
    (IsIrrepCovariant D.U Phi ∧ IsPaperChannel Phi) ↔
      ∃ l : OccurringIrrep D → ℂ, Phi = spectralMap D l ∧ trivialCoefficient D l = 1 ∧
        (∀ r, NonnegativeScalar (∑ g : G,
          (∑ a : OccurringIrrep D, l a * (D.F.dim a.val : ℂ) * character (D.F.irrep a.val) g⁻¹) *
            (Complex.normSq (Matrix.trace (eigenmatrix D P r * (D.U.rho g)ᴴ)) : ℂ))) ∧
        ∀ a : OccurringIrrep D, (∃ X : Mat n, X ≠ 0 ∧ centralMap D.U D.F a.val X = X) ∧
          ∀ X : Mat n, Phi (centralMap D.U D.F a.val X) = l a • centralMap D.U D.F a.val X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
