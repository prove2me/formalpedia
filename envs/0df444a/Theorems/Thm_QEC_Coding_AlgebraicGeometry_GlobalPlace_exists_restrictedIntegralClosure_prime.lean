-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_restrictedIntegralClosure_prime
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_restrictedIntegralClosure_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:19:32.317122+00:00
-- url     : https://prove2.me/theorems/17aaf11c-a6ab-4aaa-b191-a602d70c5c87
-- title:
--   Global Place: exists restricted Integral Closure prime
-- statement:
--   At every finite coordinate-window base, the actual integral closure
--   contains a height-one prime with precisely the originally supplied ambient
--   order. This constructs the prime, rather than assuming order compatibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RestrictedIntegralModel.lean#L48-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RestrictedIntegralModel.lean#L48-L74

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
noncomputable section
variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E)
local notation "P" => Q.restrict (F := F)
local notation "A" => GlobalPlace.valuationRing (GlobalPlace.restrict (F := F) Q)
local notation "C" => integralClosure A E
variable [Algebra (Q.restrict (F := F)).valuationRing E]
    [IsScalarTower (Q.restrict (F := F)).valuationRing F E]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_restrictedIntegralClosure_prime
    [IsDedekindDomain C] [IsFractionRing C E] :
    ∃ H : IsDedekindDomain.HeightOneSpectrum C,
      H.valuationSubringAtPrime E = Q.valuationRing ∧
        (heightOnePlace (k := k) (K := E) H).order = Q.order := by sorry
