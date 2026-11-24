-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_toH0_db774a862a06
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_toH0_db774a862a06
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:29.529798+00:00
-- url     : https://prove2.me/theorems/5133d7b4-7380-4b5b-9160-a69a9a5fe747
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cohom Map to H0 db774a862a06: P2 M Ground Theory Heights  Heights Kleiman cohom Map to H0 db774a862a06
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cohom Map to H0 db774a862a06 construction uses the P2 M Ground Theory Heights  Heights Kleiman cohom Map to H0 db774a862a06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L286-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L286-L293

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_toH0_db774a862a06 {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜') (c : ℤ)
    (m : 𝓜.piece c) : cohomMap f 0 c (toH0 𝓜 c m) = toH0 𝓜' c ⟨f.toLin m, f.map_piece c m m.2⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«cohomMap_toH0» := P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_toH0_db774a862a06
