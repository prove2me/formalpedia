-- Prove2me | Theorems.Thm_SensitivityGuardCardinality_circulant_outdegree
-- name    : SensitivityGuardCardinality.circulant_outdegree
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:19:21.632222+00:00
-- url     : https://prove2.me/theorems/1d907e3d-726b-4cb2-9d5d-82191aed9c83
-- title:
--   Translation-invariant outdegree of a masked circulant
-- statement:
--   Let $n>0$ and let a bit mask define a circulant relation on $\operatorname{Fin}(n)$. The outdegree of every vertex, excluding loops, is
--
--   $$|\{d\in\operatorname{Fin}(n):d\ne0\ \text{and the mask bit at }d\text{ is true}\}|.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/TournamentRegularDegrees.lean lines 22–42; SHA256 3248ab61a2fda8b29a7f527d5be3c7e9f0f9f9597df9ae58e1ed3f0dcf94d052; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentRegularDegrees
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
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardCardinality
end SensitivityGuardCardinality
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Regular degrees of the literal circulant and Paley guard graphs. -/
open SensitivityGuardCardinality
open SensitivityRankedConstruction SensitivityRankMapCheckpoint
open scoped Fin.CommRing

theorem SensitivityGuardCardinality.circulant_outdegree {n : ℕ} [NeZero n] (mask : ℕ) (v : Fin n) :
    (outNeighbors (circulantArc mask) v).card = (residueSupport n mask).card := by sorry
