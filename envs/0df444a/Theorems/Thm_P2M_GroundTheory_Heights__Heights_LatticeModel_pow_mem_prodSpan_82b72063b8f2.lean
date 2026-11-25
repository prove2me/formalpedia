-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_pow_mem_prodSpan_82b72063b8f2
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_pow_mem_prodSpan_82b72063b8f2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:55.571805+00:00
-- url     : https://prove2.me/theorems/13aa63a2-b503-5932-b72d-2473917b2dfa
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model pow mem prod Span 82b72063b8f2: P2 M Ground Theory Heights  Heights Lattice Model pow mem prod Span 82b72063b8f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model pow mem prod Span 82b72063b8f2 construction uses the P2 M Ground Theory Heights  Heights Lattice Model pow mem prod Span 82b72063b8f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L52-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_pow_mem_prodSpan_82b72063b8f2 {p : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L 1) (k : ℕ) :
    p ^ k ∈ prodSpan L k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«pow_mem_prodSpan» := P2M_GroundTheory_Heights__Heights_LatticeModel_pow_mem_prodSpan_82b72063b8f2
