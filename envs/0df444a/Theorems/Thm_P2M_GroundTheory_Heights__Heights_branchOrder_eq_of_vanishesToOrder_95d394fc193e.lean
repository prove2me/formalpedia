-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_branchOrder_eq_of_vanishesToOrder_95d394fc193e
-- name    : P2M_GroundTheory_Heights__Heights_branchOrder_eq_of_vanishesToOrder_95d394fc193e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:30.626822+00:00
-- url     : https://prove2.me/theorems/0e6465aa-10d3-4474-9080-6a91cd0673ca
-- title:
--   P2 M Ground Theory Heights  Heights branch Order eq of vanishes To Order 95d394fc193e: P2 M Ground Theory Heights  Heights branch Order eq of vanishes To Order 95d394fc193e
-- statement:
--   The P2 M Ground Theory Heights  Heights branch Order eq of vanishes To Order 95d394fc193e construction uses the P2 M Ground Theory Heights  Heights branch Order eq of vanishes To Order 95d394fc193e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchNormalisation.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchNormalisation.lean#L17-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_branchOrder_eq_of_vanishesToOrder_95d394fc193e {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) (f : MvPolynomial (Fin n) ℂ) (k : ℕ)
    (h : VanishesToOrder (fun t ↦ eval (c.toFun t) f) c.radius k) : branchOrder c f = k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«branchOrder_eq_of_vanishesToOrder» := P2M_GroundTheory_Heights__Heights_branchOrder_eq_of_vanishesToOrder_95d394fc193e
