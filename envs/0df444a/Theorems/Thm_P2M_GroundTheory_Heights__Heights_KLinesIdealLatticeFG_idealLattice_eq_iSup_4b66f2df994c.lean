-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_idealLattice_eq_iSup_4b66f2df994c
-- name    : P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_idealLattice_eq_iSup_4b66f2df994c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:32.62684+00:00
-- url     : https://prove2.me/theorems/1f5d1bf1-a164-4697-a772-c8cc66cd5610
-- title:
--   P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG ideal Lattice eq i Sup 4b66f2df994c: P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG ideal Lattice eq i Sup 4b66f2df994c
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG ideal Lattice eq i Sup 4b66f2df994c construction uses the P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG ideal Lattice eq i Sup 4b66f2df994c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealLatticeFG.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealLatticeFG.lean#L12-L16

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

theorem P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_idealLattice_eq_iSup_4b66f2df994c (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice a = ⨆ x, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => K) x)
      (a x : Submodule (𝓞 K) K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesIdealLatticeFG».«idealLattice_eq_iSup» := P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_idealLattice_eq_iSup_4b66f2df994c
