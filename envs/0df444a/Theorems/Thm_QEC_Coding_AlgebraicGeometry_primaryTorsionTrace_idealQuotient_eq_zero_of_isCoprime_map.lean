-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:27.922296+00:00
-- url     : https://prove2.me/theorems/5380993e-884a-4e34-8c8e-191c3a56926a
-- title:
--   Algebraic Geometry: primary Torsion Trace ideal Quotient eq zero of is Coprime map
-- statement:
--   If `J` is coprime to the extension of `p`, every finite-depth primary
--   trace on the ideal quotient `S ⧸ J` is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CoprimeQuotientTrace.lean#L81-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CoprimeQuotientTrace.lean#L81-L102

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal]
    (J : Ideal S)
    (hcop : IsCoprime (Ideal.map (algebraMap R S) p) J)
    (f : (S ⧸ J) →ₗ[R] (S ⧸ J)) (n : ℕ) :
    primaryTorsionTrace p f n = 0 := by sorry
