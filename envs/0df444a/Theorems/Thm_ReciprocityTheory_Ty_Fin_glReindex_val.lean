-- Prove2me | Theorems.Thm_ReciprocityTheory_Ty_Fin_glReindex_val
-- name    : ReciprocityTheory.Ty.Fin.glReindex_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:02.891121+00:00
-- url     : https://prove2.me/theorems/1d264d57-2b43-4713-a134-1d2683441707
-- title:
--   Fin: gl Reindex val
-- statement:
--   The Fin construction uses the gl Reindex val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/FiniteDimensionalHcSpace.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/FiniteDimensionalHcSpace.lean#L64-L65

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
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]

theorem ReciprocityTheory.Ty.Fin.glReindex_val {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (g : GL α K) : ((glReindex K e g : GL β K) : Matrix β β K) = (g : Matrix α α K).submatrix e.symm e.symm := by sorry
