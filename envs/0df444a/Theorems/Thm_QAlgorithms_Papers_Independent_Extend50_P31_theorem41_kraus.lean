-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_theorem41_kraus
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.theorem41_kraus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:50:33.046815+00:00
-- url     : https://prove2.me/theorems/f94c5531-ee51-4294-9da2-e54bb0791005
-- title:
--   Theorem 41 and Remark 42: explicit Kraus family
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Let $\Phi_l=\sum_\Theta l_\alpha P_\alpha$ be a channel. Its Choi eigenvalues $\epsilon_i^\beta$ are real and nonnegative. With $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$, the following constructs a normalized Kraus family; changing positive pivots leaves the reconstructed map unchanged:
--
--   $$
--   K_{\beta i}=\sqrt{\epsilon_i^\beta}\,[\operatorname{unvec}(v_i^\beta)]^T=\sqrt{\epsilon_i^\beta}\,V_i^\beta,\quad\Phi_l(X)=\sum_{\beta,i}K_{\beta i}XK_{\beta i}^\dagger,\quad\sum_{\beta,i}K_{\beta i}^\dagger K_{\beta i}=I_n.
--   $$
--
--   This describes the explicit Kraus family in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 18, Theorem 41 and Remark 42: explicit Kraus family

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

/-- PDF p.18, Theorem 41 and Remark 42, repaired using Appendix D pp.40--41 Eqs.(196),(201).
SOURCE CORRECTIONS: i ranges to d_beta (Eq.(93)), not |Theta|. The Kraus formula is
sqrt(choiEigenvalueVector)*(unvec(v))^T = sqrt(choiEigenvalueVector)*V, since Eq.(74) already transposes V.
This constructs one Kraus family; it does not classify all Kraus representations. -/
theorem theorem41_kraus (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ)
    (hch : IsPaperChannel (spectralMap D l)) :
    (∀ r, NonnegativeScalar (choiEigenvalueVector D P l r)) ∧
    QAlgorithms.IsKrausFamily (pivotKrausFamily D P l) ∧
    (∀ X : Mat n, spectralMap D l X = QAlgorithms.krausApply (pivotKrausFamily D P l) X) ∧
    (∀ Q : Pivots D, ∀ X : Mat n,
      QAlgorithms.krausApply (pivotKrausFamily D P l) X =
        QAlgorithms.krausApply (pivotKrausFamily D Q l) X) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
