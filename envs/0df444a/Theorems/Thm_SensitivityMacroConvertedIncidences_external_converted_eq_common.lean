-- Prove2me | Theorems.Thm_SensitivityMacroConvertedIncidences_external_converted_eq_common
-- name    : SensitivityMacroConvertedIncidences.external_converted_eq_common
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:33:53.8429+00:00
-- url     : https://prove2.me/theorems/52d67461-1b60-464b-8b23-4f8a4c4a94d2
-- title:
--   External converted destinations depend only on the source macro
-- statement:
--   For disjoint high and low sets, the converted outside destinations of a paired row whose macro differs from the source macro are exactly commonDestinations for that source macro.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroConvertedIncidences.lean lines 24–51; SHA256 24b28cd7d2787a85c228520330ec313de7c16d676acbb6a5d067793598aa23a6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IndexedGuardResiduals
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroConvertedIncidences
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerResidualPartition
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
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

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityIndexedGuardResiduals
end SensitivityIndexedGuardResiduals
namespace SensitivityMacroConvertedIncidences
end SensitivityMacroConvertedIncidences
namespace SensitivityMarkerResidualPartition
end SensitivityMarkerResidualPartition
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Equal checks from one source macro have a common set of converted
external destinations. Its size is the `counts_u` variable used by the
finite guard partition, while the original incidence sum stays separate. -/
open SensitivityMacroConvertedIncidences
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityGuardEvents SensitivityHighHeadGuardBridge
open SensitivityIndexedGuardResiduals SensitivityOperativeHeads SensitivityMarkerResidualPartition
set_option autoImplicit false
variable {M B I Color : Type} {L : ℕ}

theorem SensitivityMacroConvertedIncidences.external_converted_eq_common [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (H low : Finset (M × B)) (hdisjoint : Disjoint low H) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool) (v : M × B) :
    (converted (outsideDestinations row (pairedIndexing macroArc label internalArc) H v cutoff x)
      low).filter (fun w => w.1 ≠ v.1) = commonDestinations row macroArc label low cutoff x v.1 := by sorry
