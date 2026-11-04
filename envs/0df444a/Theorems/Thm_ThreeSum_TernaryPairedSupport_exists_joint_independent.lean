-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupport_exists_joint_independent
-- name    : ThreeSum.TernaryPairedSupport.exists_joint_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:40.022736+00:00
-- url     : https://prove2.me/theorems/327e8b6e-2979-41ce-8b6c-985685df73bb
-- title:
--   Ternary Paired Support: exists joint independent
-- statement:
--   Greedy simultaneous independence. The deliberately coarse threshold
--   `2*p^m` avoids an off-by-one affine-span convention and is a fixed constant
--   when the moment order and native prime are fixed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L57-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L57-L98

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

theorem ThreeSum.TernaryPairedSupport.exists_joint_independent (f : E → V) (g : E → W)
    (hf : Function.Injective f) (hg : Function.Injective g) (m : ℕ)
    (hcard : 2 * Fintype.card K ^ m < Fintype.card E) :
    ∃ e : Fin m → E, LinearIndependent K (fun i => f (e i)) ∧
      LinearIndependent K (fun i => g (e i)) := by sorry
