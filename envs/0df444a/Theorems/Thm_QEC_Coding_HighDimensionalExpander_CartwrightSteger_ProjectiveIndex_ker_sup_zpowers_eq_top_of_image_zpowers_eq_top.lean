-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_ker_sup_zpowers_eq_top_of_image_zpowers_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.ker_sup_zpowers_eq_top_of_image_zpowers_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:46.925522+00:00
-- url     : https://prove2.me/theorems/093b8692-1b7c-4400-88a0-ea2a65de632e
-- title:
--   Projective Index: ker sup zpowers eq top of image zpowers eq top
-- statement:
--   If one element generates the target of a surjective group homomorphism,
--   then that element together with the kernel generates the source.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L23-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L23-L41

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable {G Q : Type*} [Group G] [Group Q]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.ker_sup_zpowers_eq_top_of_image_zpowers_eq_top
    (f : G →* Q) (b : G)
    (hb : Subgroup.zpowers (f b) = ⊤) :
    f.ker ⊔ Subgroup.zpowers b = ⊤ := by sorry
