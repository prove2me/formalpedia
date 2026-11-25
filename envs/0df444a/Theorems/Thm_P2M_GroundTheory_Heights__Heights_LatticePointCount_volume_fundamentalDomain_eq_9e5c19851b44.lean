-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_fundamentalDomain_eq_9e5c19851b44
-- name    : P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_fundamentalDomain_eq_9e5c19851b44
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:37.109498+00:00
-- url     : https://prove2.me/theorems/12ff780a-102f-49c5-9eea-d22d4a8842c8
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Point Count volume fundamental Domain eq 9e5c19851b44: P2 M Ground Theory Heights  Heights Lattice Point Count volume fundamental Domain eq 9e5c19851b44
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Point Count volume fundamental Domain eq 9e5c19851b44 construction uses the P2 M Ground Theory Heights  Heights Lattice Point Count volume fundamental Domain eq 9e5c19851b44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L78-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq
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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount

theorem P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_fundamentalDomain_eq_9e5c19851b44 {r : ℕ} (c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) :
    volume (ZSpan.fundamentalDomain c) =
      ENNReal.ofReal |(EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticePointCount».«volume_fundamentalDomain_eq» := P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_fundamentalDomain_eq_9e5c19851b44
