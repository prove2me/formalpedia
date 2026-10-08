-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_lemma_5_3
-- name    : UncertainPricing.Superrep.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:44.565987+00:00
-- url     : https://prove2.me/theorems/45d1e26a-e784-45a5-8e95-7f64ccb99ac6
-- title:
--   Lemma 5.3, p. 22 — under H(μ̲, μ̄), dμ̲_t ≤ d⟨B̃̃⟩^Q_t ≤ dμ̄_t Q-a.s., stated for the law Q*
-- statement:
--   Assume $H(\underline\mu,\bar\mu)$ for the set $\mathbf P$, with $\bar\mu$ Hölder continuous, and let $Q\in\mathcal Q$ with continuous modification $\tilde{\tilde B}$ of $\tilde B$. Then
--   $$d\underline\mu_t\le d\langle\tilde{\tilde B}\rangle^Q_t\le d\bar\mu_t\qquad Q\text{-a.s.}$$
--   Equivalently, the law $Q^*$ of $\tilde{\tilde B}$ on $\Omega$ is a martingale measure satisfying $H(\underline\mu,\bar\mu)$.
--
--   Together with the representation of $\Lambda$ by $\mathcal Q$, this shows that the dual measures produce admissible models, which is what makes $\mathbf P''=\{Q^*:Q\in\mathcal Q\}$ work in Theorem 3.1.
--
--   **Formalization Note.** The statement is transferred to $Q^*$: the bracket of $\tilde{\tilde B}$ under $Q$ is the bracket of the coordinate process under its law $Q^*$. The conclusion also includes that $Q^*$ is a martingale measure (stated for §4 in Corollary 4.5 and reused on p. 22), which is needed for the bracket to be defined. $Q^*$ is a pushforward measure; being a probability is part of the conclusion, which excludes the junk zero measure.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Lemma 5.3, p. 22 (Q* and Corollary 4.5, p. 15)

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting
import Definitions.Def_UncertainPricing_Superrep_Compact

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem lemma_5_3 (T : ℝ) (hT : 0 < T) (μL μU : StieltjesFunction ℝ) (hμL : IsDistFn T μL)
    (hμU : IsDistFn T μU) (Ps : Set (Measure (Ω T)))
    (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypLU μL μU P)
    (hHol : IsHolder T μU) (Q : Measure (Ωt T)) (hQ : Q ∈ Qset Ps μU)
    (X : Set.Icc (0 : ℝ) T → Ωt T → ℝ) (hX : IsContModif Q X) :
    IsMartingaleMeasure (lawOf Q hX) ∧ HypLU μL μU (lawOf Q hX) := by sorry

end UncertainPricing.Superrep
