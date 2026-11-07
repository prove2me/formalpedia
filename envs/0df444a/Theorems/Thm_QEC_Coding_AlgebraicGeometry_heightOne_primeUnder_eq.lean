-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOne_primeUnder_eq
-- name    : QEC.Coding.AlgebraicGeometry.heightOne_primeUnder_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:26:32.487032+00:00
-- url     : https://prove2.me/theorems/ef1dc006-f33c-4d6e-8449-89e1a1e48b1a
-- title:
--   Algebraic Geometry: height One prime Under eq
-- statement:
--   The Algebraic Geometry construction uses the height One prime Under eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L256-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L256-L282

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry

theorem QEC.Coding.AlgebraicGeometry.heightOne_primeUnder_eq
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.HasGoingDown R S]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥)
    (q : Ideal S) [q.IsPrime] (hq : q.height = 1) (hle : P ≤ q.under R) :
    q.under R = P := by sorry
