-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_homogeneousComponent_map_coeffs_93ef5918ee46
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_homogeneousComponent_map_coeffs_93ef5918ee46
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:53.815794+00:00
-- url     : https://prove2.me/theorems/59685e29-dfde-4111-a127-5a35e8d20da7
-- title:
--   P2 M Ground Theory Heights  Heights Vertical homogeneous Component map coeffs 93ef5918ee46: P2 M Ground Theory Heights  Heights Vertical homogeneous Component map coeffs 93ef5918ee46
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical homogeneous Component map coeffs 93ef5918ee46 construction uses the P2 M Ground Theory Heights  Heights Vertical homogeneous Component map coeffs 93ef5918ee46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecCompDim.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecCompDim.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecCompDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_homogeneousComponent_map_coeffs_93ef5918ee46 {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«homogeneousComponent_map_coeffs» := P2M_GroundTheory_Heights__Heights_Vertical_homogeneousComponent_map_coeffs_93ef5918ee46
