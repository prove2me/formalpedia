-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_symm_apply_679901b5bc6a
-- name    : P2M_GroundTheory_Heights__Heights_relabelRingEquiv_symm_apply_679901b5bc6a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:41.702494+00:00
-- url     : https://prove2.me/theorems/9471c793-dba0-4e70-8d92-61d614b8a9af
-- title:
--   P2 M Ground Theory Heights  Heights relabel Ring Equiv symm apply 679901b5bc6a: P2 M Ground Theory Heights  Heights relabel Ring Equiv symm apply 679901b5bc6a
-- statement:
--   The P2 M Ground Theory Heights  Heights relabel Ring Equiv symm apply 679901b5bc6a construction uses the P2 M Ground Theory Heights  Heights relabel Ring Equiv symm apply 679901b5bc6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L188-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L188-L189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

theorem P2M_GroundTheory_Heights__Heights_relabelRingEquiv_symm_apply_679901b5bc6a (f : MRing ι') :
    (relabelRingEquiv ε h).symm f = rename (relabelBlocks ε h).symm f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«relabelRingEquiv_symm_apply» := P2M_GroundTheory_Heights__Heights_relabelRingEquiv_symm_apply_679901b5bc6a
