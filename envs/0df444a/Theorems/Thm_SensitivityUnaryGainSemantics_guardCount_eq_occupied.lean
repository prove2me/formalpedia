-- Prove2me | Theorems.Thm_SensitivityUnaryGainSemantics_guardCount_eq_occupied
-- name    : SensitivityUnaryGainSemantics.guardCount_eq_occupied
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:02:49.524317+00:00
-- url     : https://prove2.me/theorems/ec78f1cc-d0a5-49d7-b382-5063b09bc28b
-- title:
--   Occupied-height lists recover all higher guard counts
-- statement:
--   Let $F$ be nested. Form the list $\mathbf h$ of guard heights strictly above a cutoff $a$, one entry for each occupied check. For every threshold $t\ge a$,
--   $$
--   C_t(v,x)=\#\{h\in\mathbf h:h>t\},
--   $$
--   where the right-hand side counts list entries with multiplicity.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainSemanticBridge.lean lines 27–42; SHA256 054e30f0441976a3a16e1651d3595330566934f9379483807bb7f2ef8d0a2a01; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityUnaryGainSemantics
end SensitivityUnaryGainSemantics


/-! The full ordinary/firm unary recipe, represented by actual finite heights. -/
open SensitivityUnaryGainSemantics
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityStrictGateStates SensitivitySocketEventSupport
open SensitivityOperativeHeads SensitivityOwnTargetBounds
set_option autoImplicit false
variable {V S I Color : Type}

theorem SensitivityUnaryGainSemantics.guardCount_eq_occupied {row : RowFamily I Color 12} (hnested : Nested row)
    (guards : GuardFamily V S) (v : V) (cutoff : Fin 12) (threshold : ℕ)
    (hthreshold : cutoff.val ≤ threshold) (x : ((V × S) × I) → Bool) :
    guardCount row guards v threshold x = SensitivityUnaryGainNumeric.count threshold
      (occupiedGuardHeights row guards v cutoff x) := by sorry
