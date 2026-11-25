-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ord_prod_e2b9c1e6a97e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ord_prod_e2b9c1e6a97e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:31.451028+00:00
-- url     : https://prove2.me/theorems/8cd01a6c-3c03-47bd-ab06-17747273e7a4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical ord prod e2b9c1e6a97e: P2 M Ground Theory Heights  Heights Vertical ord prod e2b9c1e6a97e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical ord prod e2b9c1e6a97e construction uses the P2 M Ground Theory Heights  Heights Vertical ord prod e2b9c1e6a97e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormLength.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormLength.lean#L16-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module
noncomputable section
variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]

theorem P2M_GroundTheory_Heights__Heights_Vertical_ord_prod_e2b9c1e6a97e {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ord_prod» := P2M_GroundTheory_Heights__Heights_Vertical_ord_prod_e2b9c1e6a97e
