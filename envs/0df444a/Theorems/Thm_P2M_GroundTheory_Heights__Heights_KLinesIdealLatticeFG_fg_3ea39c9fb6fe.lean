-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_fg_3ea39c9fb6fe
-- name    : P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_fg_3ea39c9fb6fe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:15.884798+00:00
-- url     : https://prove2.me/theorems/20bb61b6-807c-437b-bd04-234c6d796d72
-- title:
--   P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG fg 3ea39c9fb6fe: P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG fg 3ea39c9fb6fe
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG fg 3ea39c9fb6fe construction uses the P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG fg 3ea39c9fb6fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealLatticeFG.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealLatticeFG.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealLatticeFG
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
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG

theorem P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_fg_3ea39c9fb6fe (K : Type) [Field K] [NumberField K] {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesIdealLatticeFG».«fg» := P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_fg_3ea39c9fb6fe
