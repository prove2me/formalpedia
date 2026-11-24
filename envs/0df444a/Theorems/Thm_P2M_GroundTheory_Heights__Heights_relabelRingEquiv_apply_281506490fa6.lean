-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_apply_281506490fa6
-- name    : P2M_GroundTheory_Heights__Heights_relabelRingEquiv_apply_281506490fa6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:53.095415+00:00
-- url     : https://prove2.me/theorems/aab4387a-e2dd-415e-b38e-376215a27633
-- title:
--   P2 M Ground Theory Heights  Heights relabel Ring Equiv apply 281506490fa6: P2 M Ground Theory Heights  Heights relabel Ring Equiv apply 281506490fa6
-- statement:
--   The P2 M Ground Theory Heights  Heights relabel Ring Equiv apply 281506490fa6 construction uses the P2 M Ground Theory Heights  Heights relabel Ring Equiv apply 281506490fa6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L185-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L185-L186

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

theorem P2M_GroundTheory_Heights__Heights_relabelRingEquiv_apply_281506490fa6 (f : MRing ι) :
    relabelRingEquiv ε h f = rename (relabelBlocks ε h) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«relabelRingEquiv_apply» := P2M_GroundTheory_Heights__Heights_relabelRingEquiv_apply_281506490fa6
