-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma37_characterFormulas
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma37_characterFormulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:47:33.20353+00:00
-- url     : https://prove2.me/theorems/6176bcd2-ff8d-47f3-9e3a-1cc6b1ccb547
-- title:
--   Lemma 37 and Remarks 34,38: character-only eigenvalue formulas
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Let $l_{\mathrm{id}}=1$, let $r=(\beta,i)$, and let $(s,t)$ be any positive pivot, with $p=(\widetilde P_{\beta i})_{st,st}$. Write $c_l(g)=\sum_\alpha l_\alpha d_\alpha\chi_\alpha(g^{-1})$. The following two expressions equal the Choi eigenvalue, independently of the pivot:
--
--   $$
--   \begin{aligned}\epsilon_i^\beta&=\frac1{|G|^3}\sum_g c_l(g)\left|\frac{d_\beta}{\sqrt p}\sum_h\varphi^\beta(h^{-1})_{ii}u_{ts}(h^{-1}g^{-1}h)\right|^2\\&=\frac{d_\beta}{p|G|^2}\sum_{g,h}c_l(g)\varphi^\beta(h^{-1})_{ii}u_{ts}(g^{-1})u_{st}(hgh^{-1}).\end{aligned}
--   $$
--
--   For a fixed $\alpha$, the analogous double sum, replacing $c_l(g)$ by $d_\alpha\chi_\alpha(g^{-1})$, gives $\mu_i(\alpha,\beta)$. Complete positivity is equivalent to reality and nonnegativity of all these eigenvalue expressions. The displayed squared-sum prefactor corrects the printed Eq.(82).
--
--   **Formalization Note** Scalar inequalities require zero imaginary part as well as nonnegative real part.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 16, Lemma 37 and Remarks 34,38: character-only eigenvalue formulas

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

/-- PDF pp.15--16, Lemma 37 and Remarks 34,38, with Appendix B p.39.
SOURCE CORRECTION: printed Eq.(82) has |G|^-2 outside the modulus; substitution
of Eq.(62) requires |G|^-3. Eq.(83) retains |G|^-2 after Schur reduction.
Nonnegativity is a CP criterion, never an automatic conclusion for arbitrary complex l. -/
theorem lemma37_characterFormulas (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ)
    (hl : trivialCoefficient D l = 1) :
    (∀ a : A, ∀ r : Row D, ∀ p, 0 < pivotWeight D.U D.F r.1.val r.2 p →
      muAt D a r p = doubleSumMu D a r p) ∧
    (∀ r : Row D, ∀ p, 0 < pivotWeight D.U D.F r.1.val r.2 p →
      choiEigenvalueVector D P l r = squaredSumEpsilon D l r p ∧
      choiEigenvalueVector D P l r = ∑ a : OccurringIrrep D, l a * doubleSumMu D a.val r p) ∧
    (QAlgorithms.Entanglement.IsCompletelyPositive (spectralMap D l) ↔
      ∀ r : Row D, ∀ p, 0 < pivotWeight D.U D.F r.1.val r.2 p →
        NonnegativeScalar (squaredSumEpsilon D l r p)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
