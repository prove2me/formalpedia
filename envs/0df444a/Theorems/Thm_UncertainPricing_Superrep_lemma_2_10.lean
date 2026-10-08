-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_lemma_2_10
-- name    : UncertainPricing.Superrep.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:47.656154+00:00
-- url     : https://prove2.me/theorems/5d2e5a52-cf9e-4067-ac90-40e1829ae3c7
-- title:
--   Lemma 2.10, p. 7 — a universal quadratic variation ⟨B⟩_t ∈ ℒ with ⟨B⟩_t = ⟨B⟩^P_t P-a.s. for all P, and ⟨B⟩_t ≤ μ̄_t q.s.
-- statement:
--   Let $\mathbf P$ be a set of martingale measures on $\Omega$ satisfying $H(\bar\mu)$ and let $t\in[0,T]$. There exists an element of $\mathcal L$, denoted $\langle B\rangle_t$, such that
--   $$\langle B\rangle_t=\langle B\rangle^P_t\quad P\text{-a.s. for all }P\in\mathbf P,\qquad\text{and}\qquad\langle B\rangle_t\le\bar\mu_t\quad\text{q.s.}$$
--
--   The lemma provides a single, model-independent version of the bracket, which is needed to state Lemma 2.14 and the bracket estimates of §4–§5.
--
--   **Formalization Note.** "$\langle B\rangle^P_t$" is any process $A$ that is a quadratic variation of $B$ under $P$ in the sense of the definitions file; the identity is required for every such $A$ (they agree $P$-a.s.). Under $H(\bar\mu)$ such an $A$ exists for each $P\in\mathbf P$.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Lemma 2.10, p. 7

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem lemma_2_10 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (t : Set.Icc (0 : ℝ) T) :
    ∃ q : Ω T → ℝ, InL Ps q ∧ (∀ P ∈ Ps, ∀ A, IsQuadVar P A → q =ᵐ[P] A t) ∧
      QS Ps (fun ω => q ω ≤ μU t) := by sorry

end UncertainPricing.Superrep
