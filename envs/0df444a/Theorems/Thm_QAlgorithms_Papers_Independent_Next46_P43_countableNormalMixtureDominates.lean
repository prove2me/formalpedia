-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_countableNormalMixtureDominates
-- name    : QAlgorithms.Papers.Independent.Next46.P43.countableNormalMixtureDominates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:40:23.795401+00:00
-- url     : https://prove2.me/theorems/f11b788c-8bdc-4f43-8690-a8adc4de8878
-- title:
--   Lemma 2: a countable mixture dominates all supports
-- statement:
--   Let $M$ be a complex unital von Neumann algebra admitting a faithful normal state, represented in standard form, and let $(\varphi_\theta)_{\theta\in\Theta}$ be a nonempty family of normal states. There are selected indices $s(n)\in\Theta$, strictly positive real weights $\lambda_n$, and a normal state $\omega$ such that
--
--   $$
--   \sum_n\lambda_n=1,\qquad
--   \omega=\sum_n\lambda_n\varphi_{s(n)},\qquad
--   \operatorname{supp}\varphi_\theta\leq\operatorname{supp}\omega\quad(\theta\in\Theta).
--   $$
--
--   The functional series converges in dual norm. Individual family states may be nonfaithful; finite families are represented by repeating selections. This supplies the paper's countable-mixture dominating reference.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 6, Lemma 2: a countable mixture dominates all supports

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Lemma 2, PDF p.6 and its proof. Standard form models arbitrary von Neumann
algebras and all normal states. The strictly positive probability weights and
selected states give a norm-convergent convex series of functionals, whose
normal-state sum dominates every family support. Individual states need not
be faithful. No support projector needs to be postulated. -/
theorem countableNormalMixtureDominates
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (form : QAlgorithms.Papers.Independent.Claimed50.P06.StandardForm A)
    (psi : A →L[ℂ] ℂ)
    (hPsi : QAlgorithms.Papers.Independent.Claimed50.P06.IsNormalState A psi)
    (hFaithful : QAlgorithms.Papers.Independent.Claimed50.P06.IsFaithful A psi)
    {Theta : Type*} [Nonempty Theta] (phi : Theta → A →L[ℂ] ℂ)
    (hStates : ∀ theta,
      QAlgorithms.Papers.Independent.Claimed50.P06.IsNormalState A (phi theta)) :
    ∃ (selected : ℕ → Theta) (weight : ℕ → ℝ) (omega : A →L[ℂ] ℂ),
      (∀ n, 0 < weight n) ∧ HasSum weight 1 ∧
      HasSum (fun n => (weight n : ℂ) • phi (selected n)) omega ∧
      QAlgorithms.Papers.Independent.Claimed50.P06.IsNormalState A omega ∧
      ∀ theta,
        QAlgorithms.Papers.Independent.Claimed50.P06.SupportContained A (phi theta) omega := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
