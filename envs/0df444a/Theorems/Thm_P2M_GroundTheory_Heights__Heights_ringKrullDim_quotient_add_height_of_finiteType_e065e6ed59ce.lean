-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_add_height_of_finiteType_e065e6ed59ce
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_add_height_of_finiteType_e065e6ed59ce
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:30.799868+00:00
-- url     : https://prove2.me/theorems/c310107e-fa03-427e-924b-e0ec2b79f2d4
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient add height of finite Type e065e6ed59ce: P2 M Ground Theory Heights  Heights ring Krull Dim quotient add height of finite Type e065e6ed59ce
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient add height of finite Type e065e6ed59ce construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient add height of finite Type e065e6ed59ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCodimOneCompleteIntersection.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCodimOneCompleteIntersection.lean#L14-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneCompleteIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularQuotientGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalizationAtPrimeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCodimOneCompleteIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsLocalRing
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_add_height_of_finiteType_e065e6ed59ce {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsJacobsonRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (hfin : ringKrullDim A ≠ ⊤) (q : Ideal A)
    [q.IsPrime] : ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_add_height_of_finiteType» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_add_height_of_finiteType_e065e6ed59ce
