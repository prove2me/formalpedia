-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_example55_uniform
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.example55_uniform
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:57:10.759998+00:00
-- url     : https://prove2.me/theorems/d07b9e3f-6a2d-4c67-a974-13915ffa6d04
-- title:
--   Example 55: uniform class function gives the depolarizing projector
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Take the constant function $f(g)=1$ in the character-coefficient construction. Its coefficients and resulting map are
--
--   $$
--   l_\alpha=\delta_{\alpha,\mathrm{id}},\qquad\Phi=P_{\mathrm{id}},\qquad\Phi(X)=\frac{\operatorname{Tr}X}{n}I_n.
--   $$
--
--   This describes the uniform class function gives the depolarizing projector in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 24, Example 55: uniform class function gives the depolarizing projector

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

/-- PDF p.24, Example 55 Eq.(122), with explicit depolarizing action from Eq.(58). -/
theorem example55_uniform (D : Data G A n) :
    (∀ a : OccurringIrrep D, classCoefficients D (fun _ => 1) a = if a.val = D.F.trivial then 1 else 0) ∧
    spectralMap D (classCoefficients D (fun _ => 1)) = centralMap D.U D.F D.F.trivial ∧
    ∀ X : Mat n, spectralMap D (classCoefficients D (fun _ => 1)) X =
      (Matrix.trace X / n) • (1 : Mat n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
