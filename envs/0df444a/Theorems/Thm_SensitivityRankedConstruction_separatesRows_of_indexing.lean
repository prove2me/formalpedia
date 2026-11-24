-- Prove2me | Theorems.Thm_SensitivityRankedConstruction_separatesRows_of_indexing
-- name    : SensitivityRankedConstruction.separatesRows_of_indexing
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:22.036254+00:00
-- url     : https://prove2.me/theorems/829a6d4f-0748-4b88-b417-a77247767b39
-- title:
--   A guard indexing over a covering relation separates all rows
-- statement:
--   If guards have a GuardIndexing by an arc relation that covers every pair of unequal rows, then the guards satisfy SeparatesRows.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/TournamentGuardCoverage.lean lines 15–28; SHA256 3675980c0f9f9889be8fdab852de312c270299e594e366dcc6659f604fc6e08e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GateInvariants
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentGuardCoverage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Pairwise orientation gives the guard that separates strict row colors. -/
open SensitivityRankedConstruction
open SensitivityHighHeadGuardBridge

theorem SensitivityRankedConstruction.separatesRows_of_indexing {V S : Type} {guards : GuardFamily V S}
    {arc : V → V → Prop} (indexing : GuardIndexing guards arc)
    (hcovers : CoversPairs arc) : SeparatesRows guards := by sorry
