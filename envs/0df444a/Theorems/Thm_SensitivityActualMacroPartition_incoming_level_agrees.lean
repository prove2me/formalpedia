-- Prove2me | Theorems.Thm_SensitivityActualMacroPartition_incoming_level_agrees
-- name    : SensitivityActualMacroPartition.incoming_level_agrees
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:44:57.836107+00:00
-- url     : https://prove2.me/theorems/9aa56b43-ce51-44b2-b294-954de7449545
-- title:
--   Indexed and actual incoming macro levels agree
-- statement:
--   If a numbering covers every guard head, then at each numbered head the incoming level computed from the indexed partition and indexed guard set equals the incoming level of the corresponding actual head.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActualMacroPartition.lean lines 50–71; SHA256 00c3c9a00aefd3f14b8556963bbb6609146a357581f7f45c1f0fff4fb4c2b7c5; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActualMacroPartition
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_FiniteHeadReindexing
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroIncomingHeads
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace SensitivityActualMacroPartition
end SensitivityActualMacroPartition
namespace SensitivityFiniteHeadReindexing
end SensitivityFiniteHeadReindexing
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityIndexedGuardResiduals
end SensitivityIndexedGuardResiduals
namespace SensitivityMacroConvertedIncidences
end SensitivityMacroConvertedIncidences
namespace SensitivityMacroPartitionModel
end SensitivityMacroPartitionModel
namespace SensitivityMarkerResidualPartition
end SensitivityMarkerResidualPartition
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Actual socket heads give a bounded finite partition model. It preserves
the refined incoming counts and both the raw and compressed converted
incidence counts. -/
open SensitivityActualMacroPartition
open scoped Classical BigOperators
open SensitivityFiniteHeadReindexing SensitivityMacroPartitionModel
open SensitivityRankedConstruction SensitivityGuardEvents SensitivityHighHeadGuardBridge
open SensitivityIndexedGuardResiduals SensitivityOperativeHeads SensitivityMarkerResidualPartition
open SensitivityMacroConvertedIncidences
set_option autoImplicit false
set_option maxHeartbeats 700000
variable {n L : ℕ} {M B I Color : Type}

theorem SensitivityActualMacroPartition.incoming_level_agrees (head : Fin n → M × B) (G : Finset (M × B))
    (hcover : ∀ v ∈ G, ∃ i, head i = v) (arc : (M × B) → (M × B) → Prop) (w : Fin n) :
    SensitivityMacroPartitionModel.incomingLevel (indexedPartition head) (indexedSet head G) (indexedArc head arc) w =
      SensitivityMacroIncomingHeads.incomingLevel G arc (head w) := by sorry
