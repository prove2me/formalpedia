-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_torsUnit2
-- name    : ReciprocityTheory.ChartRestriction.L1.torsUnit2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:49:10.515562+00:00
-- url     : https://prove2.me/theorems/b11a29ab-d503-403e-a174-184af5f58122
-- title:
--   L1: tors Unit2
-- statement:
--   The L1 construction uses the tors Unit2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorsUnit2.lean#L13-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorsUnit2.lean#L13-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.torsUnit2 (K : Type) [NormedField K] [IsUltrametricDist K] (g2 g3 : K) (h2 : ‖(2 : K)‖ = 1)
    (h3 : ‖(3 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ < 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1)
    (n : ℕ) (hn : ‖(n : K)‖ = 1) (hen : ¬ 2 ∣ n) (x y : K)
    (h : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Nonsingular x y) (hP : n • (Affine.Point.some x y h) = 0) : ‖x‖ = 1 := by sorry
