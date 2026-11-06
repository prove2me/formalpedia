-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_heightOne_valuationRing_order
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.heightOne_valuationRing_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:03:07.422724+00:00
-- url     : https://prove2.me/theorems/b89ee871-0b78-4c9a-88ab-5985b58b7dc7
-- title:
--   Global Place: height One valuation Ring order
-- statement:
--   The Global Place construction uses the height One valuation Ring order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialPlaceTransport.lean#L20-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialPlaceTransport.lean#L20-L39

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
attribute [local instance] QEC.Coding.AlgebraicGeometry.placeTransportDVR

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.heightOne_valuationRing_order (P : GlobalPlace k K)
    (H : IsDedekindDomain.HeightOneSpectrum P.valuationRing) :
    (heightOnePlace (k := k) (K := K) H).order = P.order := by sorry
