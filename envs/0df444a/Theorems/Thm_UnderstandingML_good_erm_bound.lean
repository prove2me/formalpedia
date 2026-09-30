-- Prove2me | Theorems.Thm_UnderstandingML_good_erm_bound
-- name    : UnderstandingML.good_erm_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:58:38.168129+00:00
-- url     : https://prove2.me/theorems/a272eb9b-cd3e-4522-8b15-88a10ac610f1
-- title:
--   Claim 29.9(1): A_good with m ≥ (1/ε) log(1/δ) examples labeled by h_A has error ≤ ε with probability ≥ 1 − δ
-- statement:
--   **Claim 29.9(1).** Let $\epsilon, \delta > 0$, $D$ a distribution over $X$ and $h_A \in H$. Let $S$ be an i.i.d. sample consisting of $m \ge \frac1\epsilon\log(\frac1\delta)$ examples, sampled according to $D$ and labeled by $h_A$. Then, with probability of at least $1 - \delta$, the hypothesis returned by $A_{good}$ will have an error of at most $\epsilon$.
--
--   Formally: $X$ countable with measurable singletons; $A_{good}$ is any ERM for $H$ returning $h_\emptyset$ on all-$\ast$ samples.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.4 pp. 407-408, Claim 29.9 part 1 with its proof

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Claim 29.9(1)** (p. 407). Let `ε, δ > 0`, `D` a distribution over `X` and `h_A ∈ H`. Let
`S` be an i.i.d. sample of `m ≥ (1/ε) log(1/δ)` examples sampled according to `D` and labeled by
`h_A`. Then, with probability of at least `1 − δ`, the hypothesis returned by `A_good` will have
an error of at most `ε`. `X` countable with measurable singletons (so that finite and cofinite
sets are measurable). -/
theorem good_erm_bound {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    (A : Learner (X × CofinLabel X) (X → CofinLabel X)) (hA : IsGoodERM A) (D : Measure X)
    [IsProbabilityMeasure D] (Aset : {A : Set X // A.Finite ∨ Aᶜ.Finite}) (ε δ : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (m : ℕ) (hm : 1 / ε * Real.log (1 / δ) ≤ m) :
    iidLaw (D.map (fun x ↦ (x, hSet Aset x))) m
      {S | ENNReal.ofReal ε < D {x | A m S x ≠ hSet Aset x}} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
