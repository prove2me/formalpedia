-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AmbientPlaceModels_prime_order
-- name    : QEC.Coding.AlgebraicGeometry.AmbientPlaceModels.prime_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:35:39.241514+00:00
-- url     : https://prove2.me/theorems/12446221-aa30-4a23-b65a-20ea930adbaf
-- title:
--   Ambient Place Models: prime order
-- statement:
--   The Ambient Place Models construction uses the prime order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AmbientPlaceModels.lean#L71-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AmbientPlaceModels.lean#L71-L72

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
noncomputable section
variable {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (F : Type*) [Field F] [Algebra k F] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace k E)

theorem QEC.Coding.AlgebraicGeometry.AmbientPlaceModels.prime_order : (heightOnePlace (k := k) (K := E) (prime F Q)).order = Q.order := by sorry
