-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_gam_550215db2da5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_gam_550215db2da5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:45.930734+00:00
-- url     : https://prove2.me/theorems/3a4ea614-49c9-46b9-a9b5-f63498f24111
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem gam 550215db2da5: P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem gam 550215db2da5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem gam 550215db2da5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem gam 550215db2da5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L102-L104

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_gam_550215db2da5 {F : SubSystem S x E} {c : ℤ} {m : E} :
    m ∈ F.gam c ↔ ∀ J, m ∈ (F.twist (twistSys S x c)).sub J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«mem_gam» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_gam_550215db2da5
