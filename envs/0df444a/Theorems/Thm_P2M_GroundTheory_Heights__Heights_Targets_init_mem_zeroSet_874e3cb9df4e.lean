-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_init_mem_zeroSet_874e3cb9df4e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_init_mem_zeroSet_874e3cb9df4e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:51.951549+00:00
-- url     : https://prove2.me/theorems/ad665d4a-de6d-4d6a-86df-f81a386873c9
-- title:
--   P2 M Ground Theory Heights  Heights Targets init mem zero Set 874e3cb9df4e: P2 M Ground Theory Heights  Heights Targets init mem zero Set 874e3cb9df4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets init mem zero Set 874e3cb9df4e construction uses the P2 M Ground Theory Heights  Heights Targets init mem zero Set 874e3cb9df4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L69-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_init_mem_zeroSet_874e3cb9df4e {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : Fin.init x ∈ zeroSet J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«init_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_Targets_init_mem_zeroSet_874e3cb9df4e
