-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary52_extension
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary52_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:55:40.899915+00:00
-- url     : https://prove2.me/theorems/3db47172-5c71-438b-982a-726c28e0a840
-- title:
--   Corollary 52: extension to all irreducible labels
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Every covariant $\Phi$ has coefficients on $\Theta$ such that every extension to all irreducible labels gives the same map. For any absent label $\gamma$, its projector, Choi image and Choi eigenvalues vanish:
--
--   $$
--   \Phi=\sum_{\gamma\in\widehat G}l_\gamma P_\gamma,\qquad\gamma\notin\Theta\ \Longrightarrow\ P_\gamma=0,\quad J(P_\gamma)=0,\quad\mu_i(\gamma,\beta)=0.
--   $$
--
--   This describes the extension to all irreducible labels in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 21, Corollary 52: extension to all irreducible labels

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

/-- PDF pp.21--22, Corollary 52 Eqs.(110),(112), absent coefficients are completely arbitrary. -/
theorem corollary52_extension (D : Data G A n) (P : Pivots D)
    (Phi : EndMat n) (hPhi : IsIrrepCovariant D.U Phi) :
    (∃ l : OccurringIrrep D → ℂ, ∀ c : A → ℂ,
      (∀ a : OccurringIrrep D, c a.val = l a) → Phi = ∑ a : A, c a • centralMap D.U D.F a) ∧
    (∀ a : A, a ∉ D.theta → centralMap D.U D.F a = 0 ∧ choi (centralMap D.U D.F a) = 0 ∧
      ∀ r : Row D, muAt D a r (P.pivot r) = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
