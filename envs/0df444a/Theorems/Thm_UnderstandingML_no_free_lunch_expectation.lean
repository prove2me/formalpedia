-- Prove2me | Theorems.Thm_UnderstandingML_no_free_lunch_expectation
-- name    : UnderstandingML.no_free_lunch_expectation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:33:44.507957+00:00
-- url     : https://prove2.me/theorems/31a963c5-799d-43cd-bd1d-f8c93d59d358
-- title:
--   Equation (5.2): for every learner A and m < |X|/2 there are D over X × {0,1} and f with L_D(f) = 0 and E_{S∼D^m}[L_D(A(S))] ≥ 1/4
-- statement:
--   **Equation (5.2)** (in the proof of Theorem 5.1). For every algorithm $A'$ that receives a training set of $m$ examples from $X \times \{0,1\}$, where $m < |X|/2$, there exist a function $f : X \to \{0,1\}$ and a distribution $D$ over $X \times \{0,1\}$ such that $L_D(f) = 0$ and
--   $$\mathbb{E}_{S \sim D^m}[L_D(A'(S))] \ge 1/4.$$
--
--   Formally: for a domain $X$ with measurable singletons, a learner $A$ for binary classification with the 0–1 loss, and $m$ with $2m < |X|$, there is a probability distribution $D$ over $X \times \{0,1\}$ with a measurable $f$ satisfying $L_D(f) = 0$ and $\int L_D(A(S))\,dD^m(S) \ge 1/4$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §5.1 p. 62, Equations (5.1)–(5.2) in the proof of Theorem 5.1, with the proof (5.3)–(5.6)

import Definitions.Def_UnderstandingML_Framework
import Mathlib.SetTheory.Cardinal.Finite

open MeasureTheory

namespace UnderstandingML

/-- **Equation (5.2)** of the proof of Theorem 5.1 (p. 62). For every algorithm `A` that receives a
training set of `m` examples from `X × {0,1}`, with `m < |X|/2`, there exist a function
`f : X → {0,1}` and a distribution `D` over `X × {0,1}` such that `L_D(f) = 0` and
`E_{S ∼ D^m}[L_D(A(S))] ≥ 1/4`. The domain has measurable singletons (Remark 3.1), and the
witness `f` is measurable. -/
theorem no_free_lunch_expectation {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Learner (X × Bool) (X → Bool)) (m : ℕ) (hm : (2 * m : ℕ∞) < ENat.card X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, Measurable f ∧ risk loss01 D f = 0) ∧
      1 / 4 ≤ ∫ S, risk loss01 D (A m S) ∂(iidLaw D m) := by sorry

end UnderstandingML
