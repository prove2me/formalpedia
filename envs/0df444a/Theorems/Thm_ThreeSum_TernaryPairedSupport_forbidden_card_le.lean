-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupport_forbidden_card_le
-- name    : ThreeSum.TernaryPairedSupport.forbidden_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:40.30077+00:00
-- url     : https://prove2.me/theorems/8e32d3c1-f23b-41ea-bbf0-3e430a4a33d4
-- title:
--   Ternary Paired Support: forbidden card le
-- statement:
--   The Ternary Paired Support construction uses the forbidden card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L34-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L34-L52

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

theorem ThreeSum.TernaryPairedSupport.forbidden_card_le {j : ℕ} (f : E → V) (hf : Function.Injective f)
    (v : Fin j → V) (hv : LinearIndependent K v) :
    (univ.filter fun e => f e ∈ Submodule.span K (Set.range v)).card ≤
      Fintype.card K ^ j := by sorry
