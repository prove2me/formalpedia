-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_gam_089b125b1417
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_gam_089b125b1417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:03.622839+00:00
-- url     : https://prove2.me/theorems/4457a15a-1a4a-454e-b809-e1a9bd86a5e5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem gam 089b125b1417: P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem gam 089b125b1417
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem gam 089b125b1417 construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem gam 089b125b1417 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L106-L112

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_gam_089b125b1417 (F : SubSystem S x E) {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) {c : ℤ}
    {m : E} (hm : m ∈ F.gam c) : aeval x f • m ∈ F.gam (c + d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«smul_mem_gam» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_gam_089b125b1417
