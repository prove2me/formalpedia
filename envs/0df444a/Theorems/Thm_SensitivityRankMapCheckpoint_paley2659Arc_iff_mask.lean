-- Prove2me | Theorems.Thm_SensitivityRankMapCheckpoint_paley2659Arc_iff_mask
-- name    : SensitivityRankMapCheckpoint.paley2659Arc_iff_mask
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:57.546803+00:00
-- url     : https://prove2.me/theorems/6870d424-0bb7-459d-a6df-4d014f8f7a03
-- title:
--   Bit-mask representation of the Paley tournament
-- statement:
--   For vertices $x,y\in\mathbb Z/2659\mathbb Z$, the Paley arc relation, defined by a nonzero square displacement, agrees exactly with the literal circulant bit mask:
--   $$
--   x\longrightarrow y
--   \quad\Longleftrightarrow\quad
--   \operatorname{paley2659Mask}\bigl((y-x)\bmod2659\bigr)=1.
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/CheckpointTournaments.lean lines 117–140; SHA256 5c72e65c1dabf4353618467cf5ac22eb0706243af7d3fd193511a9de00120ea1; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointTournaments
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal.TournamentHighRows
end Sensitivity213981Formal.TournamentHighRows
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Full tournament laws for the actual graphs, including the typed API. -/
open SensitivityRankMapCheckpoint
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open Sensitivity213981Formal.TournamentHighRows
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem SensitivityRankMapCheckpoint.paley2659Arc_iff_mask (x y : Fin 2659) :
    paley2659Arc x y ↔ circulantArc paley2659Mask x y := by sorry
