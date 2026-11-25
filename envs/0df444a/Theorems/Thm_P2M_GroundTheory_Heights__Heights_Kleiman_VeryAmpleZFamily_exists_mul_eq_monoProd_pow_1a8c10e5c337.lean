-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_eq_monoProd_pow_1a8c10e5c337
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_eq_monoProd_pow_1a8c10e5c337
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:11:29.10641+00:00
-- url     : https://prove2.me/theorems/ff5e9a40-efb2-45bb-9bc9-d279ae67e44f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul eq mono Prod pow 1a8c10e5c337: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul eq mono Prod pow 1a8c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul eq mono Prod pow 1a8c10e5c337 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul eq mono Prod pow 1a8c10e5c337 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L98-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L98-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_eq_monoProd_pow_1a8c10e5c337 {T : Finset (Fin (r + 1))} {s : Poly S r} (hs : s ∈ monos T) :
    ∃ (k : ℕ) (t : Poly S r), t ∈ monos T ∧ s * t = AmpleAffineGen.monoProd T ^ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZFamily».«exists_mul_eq_monoProd_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_eq_monoProd_pow_1a8c10e5c337
