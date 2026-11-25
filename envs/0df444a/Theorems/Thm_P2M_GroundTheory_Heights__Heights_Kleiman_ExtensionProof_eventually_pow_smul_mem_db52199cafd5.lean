-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_eventually_pow_smul_mem_db52199cafd5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_eventually_pow_smul_mem_db52199cafd5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:01.305301+00:00
-- url     : https://prove2.me/theorems/85fc212c-d97d-4e8b-86b4-c7f0b6603fca
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof eventually pow smul mem db52199cafd5: P2 M Ground Theory Heights  Heights Kleiman Extension Proof eventually pow smul mem db52199cafd5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof eventually pow smul mem db52199cafd5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof eventually pow smul mem db52199cafd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L116-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L116-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
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
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_eventually_pow_smul_mem_db52199cafd5 (F : SubFamily S x E) {i : Fin (N + 1)} (hi : x i ≠ 0) {y : E}
    (hy : y ∈ F.sub (singleChart hi)) (J : Chart x) :
    ∀ᶠ n : ℕ in Filter.atTop, x i ^ n • y ∈ (F.twist (twistSys S x (n : ℤ))).sub J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«eventually_pow_smul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_eventually_pow_smul_mem_db52199cafd5
