-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_polyBasis_apply_c1352a7f2763
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_polyBasis_apply_c1352a7f2763
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:24.819127+00:00
-- url     : https://prove2.me/theorems/9c5c1e32-dfd4-4c6b-8093-04f845c8b8f7
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible poly Basis apply c1352a7f2763: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible poly Basis apply c1352a7f2763
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible poly Basis apply c1352a7f2763 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible poly Basis apply c1352a7f2763 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L48-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
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
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_polyBasis_apply_c1352a7f2763 {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«polyBasis_apply» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_polyBasis_apply_c1352a7f2763
