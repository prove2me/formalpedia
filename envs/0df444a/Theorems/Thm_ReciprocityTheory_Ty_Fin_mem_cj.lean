-- Prove2me | Theorems.Thm_ReciprocityTheory_Ty_Fin_mem_cj
-- name    : ReciprocityTheory.Ty.Fin.mem_cj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:11.470894+00:00
-- url     : https://prove2.me/theorems/7e8c48a3-3d87-47ae-8d4b-417a9ed4c6e0
-- title:
--   Fin: mem cj
-- statement:
--   The Fin construction uses the mem cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/FiniteDimensionalHcSpace.lean#L47-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/FiniteDimensionalHcSpace.lean#L47-L47

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_HCDisjointO
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_FiniteDimensionalHcSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open ReciprocityTheory ReciprocityTheory.Ty ReciprocityTheory.Ty.Fin
variable {Γ : Type} [Group Γ]

theorem ReciprocityTheory.Ty.Fin.mem_cj {x h : Γ} {B : Subgroup Γ} : h ∈ cj x B ↔ x * h * x⁻¹ ∈ B := by sorry
