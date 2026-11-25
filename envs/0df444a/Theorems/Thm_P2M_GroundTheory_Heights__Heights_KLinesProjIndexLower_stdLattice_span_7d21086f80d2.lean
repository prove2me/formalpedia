-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_span_7d21086f80d2
-- name    : P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_span_7d21086f80d2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:03.14617+00:00
-- url     : https://prove2.me/theorems/6797b8ba-5aa3-5223-b31a-c5893b6881ef
-- title:
--   P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice span 7d21086f80d2: P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice span 7d21086f80d2
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice span 7d21086f80d2 construction uses the P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice span 7d21086f80d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjIndexLower.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjIndexLower.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProjIndexLower
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
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesProjIndexLower

theorem P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_span_7d21086f80d2 (K : Type) [Field K] [NumberField K] (k : ℕ) :
    Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) : Set (Fin k → K)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesProjIndexLower».«stdLattice_span» := P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_span_7d21086f80d2
