-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupport_span_card_eq
-- name    : ThreeSum.TernaryPairedSupport.span_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:36.495189+00:00
-- url     : https://prove2.me/theorems/ceecf5cb-7bba-4127-8ea8-5d6a2215700c
-- title:
--   Ternary Paired Support: span card eq
-- statement:
--   The Ternary Paired Support construction uses the span card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L26-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L26-L32

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupport
open Finset
attribute [local instance] Classical.propDecidable
variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]

theorem ThreeSum.TernaryPairedSupport.span_card_eq {j : ℕ} (v : Fin j → V) (hv : LinearIndependent K v) :
    Nat.card (Submodule.span K (Set.range v)) = Fintype.card K ^ j := by sorry
