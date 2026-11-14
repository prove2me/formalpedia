-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_product_delete_one_coordinate
-- name    : StabilityDichotomies.Bijunctive.iid_product_delete_one_coordinate
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:42:06.948726+00:00
-- url     : https://prove2.me/theorems/3de75db9-b555-4412-bb7c-08b80495083a
-- title:
--   Deleting one coordinate preserves the iid product law
-- statement:
--   For a finite independent identically distributed real vector, discard one specified coordinate and reindex the others. The resulting vector has the corresponding iid product distribution. This supplies the priority marginal in the common-seed comparison of an instance with one occurrence deleted.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, common-randomness deletion coupling.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function

theorem StabilityDichotomies.Bijunctive.iid_product_delete_one_coordinate {α β : Type} [Fintype α] [Fintype β]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (e : α ≃ Option β) :
    Measure.map (fun p : α → ℝ => fun i : β => p (e.symm (some i)))
      (Measure.pi (fun _ : α => ν)) = Measure.pi (fun _ : β => ν) := by
  sorry
