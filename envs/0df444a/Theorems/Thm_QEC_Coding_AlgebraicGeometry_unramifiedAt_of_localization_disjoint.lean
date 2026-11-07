-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_unramifiedAt_of_localization_disjoint
-- name    : QEC.Coding.AlgebraicGeometry.unramifiedAt_of_localization_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:27:46.7222+00:00
-- url     : https://prove2.me/theorems/703eeaa4-5c93-4dc6-956b-4e322ab81805
-- title:
--   Algebraic Geometry: unramified At of localization disjoint
-- statement:
--   The Algebraic Geometry construction uses the unramified At of localization disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalVerticalUnramified.lean#L52-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalVerticalUnramified.lean#L52-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.unramifiedAt_of_localization_disjoint
    {R C D : Type*} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra C D] [IsScalarTower R C D]
    (M : Submonoid C) [IsLocalization M D] [Algebra.FormallyUnramified R D]
    (q : Ideal C) [q.IsPrime] (hd : Disjoint (M : Set C) (q : Set C)) :
    Algebra.IsUnramifiedAt R q := by sorry
