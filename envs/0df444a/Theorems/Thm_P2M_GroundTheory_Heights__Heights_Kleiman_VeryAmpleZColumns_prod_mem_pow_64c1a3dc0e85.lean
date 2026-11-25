-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_prod_mem_pow_64c1a3dc0e85
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_prod_mem_pow_64c1a3dc0e85
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:38.943805+00:00
-- url     : https://prove2.me/theorems/6a6ffe26-e793-4b05-b6c6-c2b42e333e9e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns prod mem pow 64c1a3dc0e85: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns prod mem pow 64c1a3dc0e85
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns prod mem pow 64c1a3dc0e85 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns prod mem pow 64c1a3dc0e85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L22-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_prod_mem_pow_64c1a3dc0e85 {I : Chart x} (Q : Submodule (chartRing S x I) Ω) (h : Fin (r + 1) → Ω)
    (hh : ∀ j, h j ∈ Q) (T : Finset (Fin (r + 1))) : ∏ j ∈ T, h j ∈ Q ^ T.card := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZColumns».«prod_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_prod_mem_pow_64c1a3dc0e85
