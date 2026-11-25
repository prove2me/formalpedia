-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_retract_fad49f66fb1a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_retract_fad49f66fb1a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:52.657334+00:00
-- url     : https://prove2.me/theorems/10335c71-9938-44db-a30b-f020416819ca
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cohom Map retract fad49f66fb1a: P2 M Ground Theory Heights  Heights Kleiman cohom Map retract fad49f66fb1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cohom Map retract fad49f66fb1a construction uses the P2 M Ground Theory Heights  Heights Kleiman cohom Map retract fad49f66fb1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCohomRetract.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCohomRetract.lean#L28-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCohomRetract
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
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_retract_fad49f66fb1a {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'}
    (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜) (hgf : Function.LeftInverse g.toLin f.toLin)
    (i : ℕ) (c : ℤ) : Function.LeftInverse (cohomMap g i c) (cohomMap f i c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«cohomMap_retract» := P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_retract_fad49f66fb1a
