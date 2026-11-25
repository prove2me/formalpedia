-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_aeval_mem_pow_250a3eb5ea29
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_aeval_mem_pow_250a3eb5ea29
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:02.709542+00:00
-- url     : https://prove2.me/theorems/b7cbd966-5f55-4ec5-99ad-2577f78cd886
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily aeval mem pow 250a3eb5ea29: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily aeval mem pow 250a3eb5ea29
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily aeval mem pow 250a3eb5ea29 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily aeval mem pow 250a3eb5ea29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L20-L43

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_aeval_mem_pow_250a3eb5ea29 {I : Chart x} {Q : Submodule (chartRing S x I) Ω} (hQ : ∀ l, h l ∈ Q)
    {f : MvPolynomial (Fin (r + 1)) S} {e : ℕ} (hf : f.IsHomogeneous e) : aeval h f ∈ Q ^ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZFamily».«aeval_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_aeval_mem_pow_250a3eb5ea29
