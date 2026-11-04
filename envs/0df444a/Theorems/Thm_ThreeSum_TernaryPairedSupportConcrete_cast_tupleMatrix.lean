-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_cast_tupleMatrix
-- name    : ThreeSum.TernaryPairedSupportConcrete.cast_tupleMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:34.147275+00:00
-- url     : https://prove2.me/theorems/a42d5809-85c6-46cf-8294-6846159ff736
-- title:
--   Ternary Paired Support Concrete: cast tuple Matrix
-- statement:
--   The Ternary Paired Support Concrete construction uses the cast tuple Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L58-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L58-L65

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]
variable {P W D : Type*} [Fintype P] [Fintype K]
  [AddCommGroup W] [Module K W] [Fintype W] [DecidableEq D]

theorem ThreeSum.TernaryPairedSupportConcrete.cast_tupleMatrix {J m : ℕ} (L R : P → Fin J → ℤ) (e : Fin m → P) :
    (fun i j => (tupleMatrix L R e i j : K)) =
      fun i => flatten J (taggedEndpoints (K := K)
        (fun i j => (L (e i) j : K)) (fun i j => (R (e i) j : K)) i) := by sorry
