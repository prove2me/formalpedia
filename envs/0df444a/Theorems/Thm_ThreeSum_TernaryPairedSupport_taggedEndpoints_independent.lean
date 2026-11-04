-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupport_taggedEndpoints_independent
-- name    : ThreeSum.TernaryPairedSupport.taggedEndpoints_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:41.441951+00:00
-- url     : https://prove2.me/theorems/1dccd146-209b-4c3f-b6d1-368d11f9e720
-- title:
--   Ternary Paired Support: tagged Endpoints independent
-- statement:
--   The two independent affine families and the two endpoint tags force
--   full paired rank. This is the exact implication needed by the determinant
--   potential; untagged or separately marginal rank claims do not suffice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L110-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L110-L152

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
variable {ι : Type*} [Fintype ι]

theorem ThreeSum.TernaryPairedSupport.taggedEndpoints_independent (L R : ι → V) (H : V →ₗ[K] W) (o : W)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : LinearIndependent K (fun i => (L i+R i,(1 : K))))
    (hleft : LinearIndependent K (fun i => (H (L i),(1 : K)))) :
    LinearIndependent K (taggedEndpoints (K := K) L R) := by sorry
