-- Prove2me | Theorems.Thm_UpperTheory_Mu_torsionOrder_le
-- name    : UpperTheory.Mu.torsionOrder_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:31.640036+00:00
-- url     : https://prove2.me/theorems/4d279a79-cae3-48a6-bc44-38bbc62798e6
-- title:
--   Mu: torsion Order le
-- statement:
--   The Mu construction uses the torsion Order le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/Monomial.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/Monomial.lean#L52-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_torsionOrder_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]

theorem UpperTheory.Mu.torsionOrder_le (K : Type) [Field K] [NumberField K] : Units.torsionOrder K ≤ 2 * Module.finrank ℚ K ^ 2 := by sorry
