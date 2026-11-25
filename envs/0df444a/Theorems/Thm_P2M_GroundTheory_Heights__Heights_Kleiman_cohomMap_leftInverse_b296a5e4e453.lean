-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_leftInverse_b296a5e4e453
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_leftInverse_b296a5e4e453
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:37.188518+00:00
-- url     : https://prove2.me/theorems/d3250f33-e4c6-4ea6-aadb-7d35895f45e9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cohom Map left Inverse b296a5e4e453: P2 M Ground Theory Heights  Heights Kleiman cohom Map left Inverse b296a5e4e453
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cohom Map left Inverse b296a5e4e453 construction uses the P2 M Ground Theory Heights  Heights Kleiman cohom Map left Inverse b296a5e4e453 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L295-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L295-L307

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_leftInverse_b296a5e4e453 {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜')
    (g : GradedHom 𝓜' 𝓜) (hfg : ∀ m, g.toLin (f.toLin m) = m) (i : ℕ) (c : ℤ) (y : cohom 𝓜 i c) :
    cohomMap g i c (cohomMap f i c y) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«cohomMap_leftInverse» := P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_leftInverse_b296a5e4e453
