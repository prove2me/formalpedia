-- Prove2me | Theorems.Thm_P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___eq_top_iff_ideal_eq_top_b681c76d4d78
-- name    : P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___eq_top_iff_ideal_eq_top_b681c76d4d78
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:51.046507+00:00
-- url     : https://prove2.me/theorems/b80f1ffe-b5e1-58bc-b509-bac95b884bf1
-- title:
--   P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   eq top iff ideal eq top b681c76d4d78: P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   eq top iff ideal eq top b681c76d4d78
-- statement:
--   The P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   eq top iff ideal eq top b681c76d4d78 construction uses the P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   eq top iff ideal eq top b681c76d4d78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L213-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L213-L247

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

theorem P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___eq_top_iff_ideal_eq_top_b681c76d4d78 {Y : Scheme.{u}} (I : Y.IdealSheafData) {V : Y.Opens}
    (hV : IsAffineOpen V) : I.comap V.ι = ⊤ ↔ I.ideal ⟨V, hV⟩ = ⊤ := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«comap_ι_eq_top_iff_ideal_eq_top» := P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___eq_top_iff_ideal_eq_top_b681c76d4d78
