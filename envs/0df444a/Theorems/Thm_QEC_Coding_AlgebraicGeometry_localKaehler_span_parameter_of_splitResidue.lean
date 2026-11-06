-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_localKaehler_span_parameter_of_splitResidue
-- name    : QEC.Coding.AlgebraicGeometry.localKaehler_span_parameter_of_splitResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:01:49.859713+00:00
-- url     : https://prove2.me/theorems/c77ddde0-d99c-49a3-9964-b348c516ccac
-- title:
--   Algebraic Geometry: local Kaehler span parameter of split Residue
-- statement:
--   A genuine split residue map and principal maximal ideal generate the finite local Kahler module by the parameter differential, using Nakayama.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalKaehlerCyclic.lean#L23-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalKaehlerCyclic.lean#L23-L49

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [CommRing k] [CommRing V] [Algebra k V]
variable [IsLocalRing V] [Algebra.EssFiniteType k V]

theorem QEC.Coding.AlgebraicGeometry.localKaehler_span_parameter_of_splitResidue
    (e : V →ₐ[k] k) (he : RingHom.ker e = IsLocalRing.maximalIdeal V)
    (pi : V) (hpi : IsLocalRing.maximalIdeal V = Ideal.span {pi}) :
    Submodule.span V {KaehlerDifferential.D k V pi} = ⊤ := by sorry
