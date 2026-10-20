-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_retainedComponents_spec
-- name    : SoficGroups.SourceCompressionRetainedDiscard.retainedComponents_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/7d9c20ac-c02d-43a4-b1b4-5665dacc7490
-- title:
--   SoficGroups.SourceCompressionRetainedDiscard.retainedComponents_spec
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceCompressionRetainedDiscard.retainedComponents_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ)
    (C : Finset V)
    (hC : C ∈ retainedComponents P Q T b eta) :
    C ∈ P.parts ∧
      SoficGroups.maximumOverlapPart Q C ∈ Q.parts ∧
      (1 - eta) * (C.card : ℝ) ≤
        ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ) ∧
      ∃ y ∈ C ∩ SoficGroups.maximumOverlapPart Q C,
        b (T.symm y) = b y := by sorry
