-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_polyBasis_apply_ba9b92bb4178
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_polyBasis_apply_ba9b92bb4178
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:01.030427+00:00
-- url     : https://prove2.me/theorems/e38b048d-c443-54fe-b0d5-44ec3f7c41ee
-- title:
--   P2 M Ground Theory Heights  Heights Vertical poly Basis apply ba9b92bb4178: P2 M Ground Theory Heights  Heights Vertical poly Basis apply ba9b92bb4178
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical poly Basis apply ba9b92bb4178 construction uses the P2 M Ground Theory Heights  Heights Vertical poly Basis apply ba9b92bb4178 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormEval.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormEval.lean#L46-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
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
open MvPolynomial TensorProduct
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_polyBasis_apply_ba9b92bb4178 {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«polyBasis_apply» := P2M_GroundTheory_Heights__Heights_Vertical_polyBasis_apply_ba9b92bb4178
