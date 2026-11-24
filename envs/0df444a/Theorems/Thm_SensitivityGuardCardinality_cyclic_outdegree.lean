-- Prove2me | Theorems.Thm_SensitivityGuardCardinality_cyclic_outdegree
-- name    : SensitivityGuardCardinality.cyclic_outdegree
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:19:31.545258+00:00
-- url     : https://prove2.me/theorems/8bce6324-000e-4e7c-8a8d-f7d6f43797d5
-- title:
--   Translation-invariant outdegree of the cyclic relation
-- statement:
--   Let $n>0$. In the cyclic relation on $\operatorname{Fin}(n)$, the outdegree of every vertex equals the size of the displacement support
--
--   $$\{d\in\operatorname{Fin}(n):0<d\le\lfloor n/2\rfloor\}.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/TournamentRegularDegrees.lean lines 44–64; SHA256 3248ab61a2fda8b29a7f527d5be3c7e9f0f9f9597df9ae58e1ed3f0dcf94d052; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentRegularDegrees
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentRegularDegrees
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

theorem SensitivityGuardCardinality.cyclic_outdegree {n : ℕ} [NeZero n] (v : Fin n) :
    (outNeighbors cyclicArc v).card = (cyclicSupport n).card := by sorry
