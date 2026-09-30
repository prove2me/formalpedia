-- Prove2me | Theorems.Thm_UnderstandingML_no_free_lunch
-- name    : UnderstandingML.no_free_lunch
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:35:48.556459+00:00
-- url     : https://prove2.me/theorems/63b65596-2c5e-41f8-a841-527509a51edc
-- title:
--   Theorem 5.1 (No-Free-Lunch): for every learner A and m < |X|/2 there is D over X × {0,1} with some L_D(f) = 0 and P_{S∼D^m}[L_D(A(S)) ≥ 1/8] ≥ 1/7
-- statement:
--   **Theorem 5.1 (No-Free-Lunch).** Let $A$ be any learning algorithm for the task of binary classification with respect to the $0-1$ loss over a domain $X$. Let $m$ be any number smaller than $|X|/2$, representing a training set size. Then, there exists a distribution $D$ over $X \times \{0,1\}$ such that:
--   1. There exists a function $f : X \to \{0,1\}$ with $L_D(f) = 0$.
--   2. With probability of at least $1/7$ over the choice of $S \sim D^m$ we have that $L_D(A(S)) \ge 1/8$.
--
--   Formally: for a domain $X$ with measurable singletons, a learner $A$ and $m$ with $2m < |X|$, there is a probability distribution $D$ over $X \times \{0,1\}$ such that some measurable $f$ has $L_D(f) = 0$, and there is a measurable set $E$ of samples of size $m$, of $D^m$-probability at least $1/7$, on every element of which $L_D(A(S)) \ge 1/8$ (the strong, inner form of "with probability at least $1/7$").
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §5.1 pp. 61-63, Theorem 5.1 with its proof

import Definitions.Def_UnderstandingML_Framework
import Mathlib.SetTheory.Cardinal.Finite

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 5.1 (No-Free-Lunch)** (p. 61). Let `A` be any learning algorithm for the task of
binary classification with respect to the 0–1 loss over a domain `X`. Let `m` be any number
smaller than `|X|/2`, representing a training set size. Then there exists a distribution `D`
over `X × {0,1}` such that: (1) there exists a function `f : X → {0,1}` with `L_D(f) = 0`;
(2) with probability of at least `1/7` over the choice of `S ∼ D^m` we have `L_D(A(S)) ≥ 1/8`.
Clause (2) is stated in the strong form: a measurable set of samples of probability at least
`1/7` on which `L_D(A(S)) ≥ 1/8`. The domain has measurable singletons (Remark 3.1), and the
witness `f` is measurable. -/
theorem no_free_lunch {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Learner (X × Bool) (X → Bool)) (m : ℕ) (hm : (2 * m : ℕ∞) < ENat.card X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, Measurable f ∧ risk loss01 D f = 0) ∧
      ∃ E : Set (Fin m → X × Bool), MeasurableSet E ∧
        E ⊆ {S | 1 / 8 ≤ risk loss01 D (A m S)} ∧ ENNReal.ofReal (1 / 7) ≤ iidLaw D m E := by sorry

end UnderstandingML
