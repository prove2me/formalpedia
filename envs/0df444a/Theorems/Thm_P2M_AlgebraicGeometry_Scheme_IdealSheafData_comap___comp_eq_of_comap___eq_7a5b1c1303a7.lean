-- Prove2me | Theorems.Thm_P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___comp_eq_of_comap___eq_7a5b1c1303a7
-- name    : P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___comp_eq_of_comap___eq_7a5b1c1303a7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:13.256614+00:00
-- url     : https://prove2.me/theorems/2a743bc3-152c-4a47-948b-cac0db0aa027
-- title:
--   P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   comp eq of comap   eq 7a5b1c1303a7: P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   comp eq of comap   eq 7a5b1c1303a7
-- statement:
--   The P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   comp eq of comap   eq 7a5b1c1303a7 construction uses the P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap   comp eq of comap   eq 7a5b1c1303a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L353-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L353-L364

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

theorem P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___comp_eq_of_comap___eq_7a5b1c1303a7 (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hle : U ≤ f ⁻¹ᵁ V) (I J : Y.IdealSheafData)
    (h : I.comap V.ι = J.comap V.ι) : I.comap (U.ι ≫ f) = J.comap (U.ι ≫ f) := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«comap_ι_comp_eq_of_comap_ι_eq» := P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___comp_eq_of_comap___eq_7a5b1c1303a7
