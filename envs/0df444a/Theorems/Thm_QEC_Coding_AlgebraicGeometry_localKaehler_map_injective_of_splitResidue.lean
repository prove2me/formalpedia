-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_localKaehler_map_injective_of_splitResidue
-- name    : QEC.Coding.AlgebraicGeometry.localKaehler_map_injective_of_splitResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:04:51.794973+00:00
-- url     : https://prove2.me/theorems/0f661778-bb99-42a3-b7a3-f7d6a41b75b7
-- title:
--   Algebraic Geometry: local Kaehler map injective of split Residue
-- statement:
--   Derived cyclicity and a nonzero parameter differential under a faithful field embedding make the actual local differential map injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalKaehlerCyclic.lean#L58-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalKaehlerCyclic.lean#L58-L80

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [CommRing k] [CommRing V] [Algebra k V]
variable [IsLocalRing V] [Algebra.EssFiniteType k V]
variable (K : Type*) [Field K] [Algebra k K] [Algebra V K]
variable [IsScalarTower k V K] [SMulCommClass k V K]

theorem QEC.Coding.AlgebraicGeometry.localKaehler_map_injective_of_splitResidue
    (e : V →ₐ[k] k) (he : RingHom.ker e = IsLocalRing.maximalIdeal V)
    (pi : V) (hpi : IsLocalRing.maximalIdeal V = Ideal.span {pi})
    (hfaith : Function.Injective (algebraMap V K))
    (hd : KaehlerDifferential.D k K (algebraMap V K pi) ≠ 0) :
    Function.Injective (KaehlerDifferential.map k k V K) := by sorry
