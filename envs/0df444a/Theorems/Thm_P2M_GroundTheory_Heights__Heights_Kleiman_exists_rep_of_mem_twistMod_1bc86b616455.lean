-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_rep_of_mem_twistMod_1bc86b616455
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_rep_of_mem_twistMod_1bc86b616455
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:44.646099+00:00
-- url     : https://prove2.me/theorems/79e1a254-dfb9-4ce2-b9dc-15828a44ae25
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists rep of mem twist Mod 1bc86b616455: P2 M Ground Theory Heights  Heights Kleiman exists rep of mem twist Mod 1bc86b616455
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists rep of mem twist Mod 1bc86b616455 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists rep of mem twist Mod 1bc86b616455 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L64-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_rep_of_mem_twistMod_1bc86b616455 (n : ℕ) {j : Fin (N + 1)} (hj : y j ≠ 0) {z : Ω}
    (hz : z ∈ twistMod S y (n : ℤ) (singleChart hj)) :
    ∃ (g s : Poly S N) (e : ℕ), s ∈ monos ({j} : Finset (Fin (N + 1))) ∧ s.IsHomogeneous e ∧
      g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_rep_of_mem_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_rep_of_mem_twistMod_1bc86b616455
