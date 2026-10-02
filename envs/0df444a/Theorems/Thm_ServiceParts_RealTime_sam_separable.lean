-- Prove2me | Theorems.Thm_ServiceParts_RealTime_sam_separable
-- name    : ServiceParts.RealTime.sam_separable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T00:19:22.004873+00:00
-- url     : https://prove2.me/theorems/f4d27446-7793-43d7-9d5f-0d8bd83c2f7d
-- title:
--   Section 10.4.1 — SAM is separable by item: Z* = Σ_i Z*_i
-- statement:
--   Let $I$ be a finite set of items sharing the finite set $J$ of bases, each item with its own data. Then the multi-item stock allocation problem $\mathrm{SAM}$ separates by item:
--
--   1. a shipment plan $y = (y_i)_{i \in I}$ is optimal for $\mathrm{SAM}$ if and only if, for every item $i$, $y_i$ is optimal for $\mathrm{SAM}_i$;
--   2. if $y$ is optimal for $\mathrm{SAM}$ and each $z_i$ is optimal for $\mathrm{SAM}_i$, the optimal values satisfy
--   $$Z^* = \sum_{i \in I} Z^*_i,$$
--   where $Z^*$ is the objective value of $y$ in $\mathrm{SAM}$ and $Z^*_i$ that of $z_i$ in $\mathrm{SAM}_i$.
--
--   This reduces the chapter's allocation problem to one problem per item, which is the setting of Theorem 15.
--
--   **Formalization Note** The book states the separation for the optimal values. The statement also characterizes the optimal plans; the value identity follows from that characterization.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 236, Section 10.4.1

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_SAM

open MeasureTheory

namespace ServiceParts.RealTime

/-- Section 10.4.1, p. 236: `SAM` is separable by item. A vector of shipments is optimal for
the multi-item problem `SAM` exactly when each item's shipments are optimal for `SAM_i`, and
the optimal value of `SAM` is the sum of the optimal values of the `SAM_i`,
`Z* = Σ_{i∈I} Z*_i`. -/
theorem sam_separable {I J : Type*} [Fintype I] [Fintype J] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (M : I → ItemModel J Ω P) :
    (∀ y : I → J → ℕ → ℕ, IsMultiSAMOptimal M y ↔ ∀ i, IsSAMOptimal (M i) (y i)) ∧
      ∀ y z : I → J → ℕ → ℕ, IsMultiSAMOptimal M y → (∀ i, IsSAMOptimal (M i) (z i)) →
        multiSamObjective M y = ∑ i, samObjective (M i) (z i) := by sorry

end ServiceParts.RealTime
