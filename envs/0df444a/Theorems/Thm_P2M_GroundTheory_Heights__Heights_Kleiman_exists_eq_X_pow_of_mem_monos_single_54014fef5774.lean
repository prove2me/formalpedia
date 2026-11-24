-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_X_pow_of_mem_monos_single_54014fef5774
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_X_pow_of_mem_monos_single_54014fef5774
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:45.673903+00:00
-- url     : https://prove2.me/theorems/078be6c1-ccca-4397-b0c7-50983887699c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists eq X pow of mem monos single 54014fef5774: P2 M Ground Theory Heights  Heights Kleiman exists eq X pow of mem monos single 54014fef5774
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists eq X pow of mem monos single 54014fef5774 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists eq X pow of mem monos single 54014fef5774 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L51-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_X_pow_of_mem_monos_single_54014fef5774 {s : Poly S N} (hs : s ∈ monos {j}) :
    ∃ n : ℕ, s = X j ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_eq_X_pow_of_mem_monos_single» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_X_pow_of_mem_monos_single_54014fef5774
