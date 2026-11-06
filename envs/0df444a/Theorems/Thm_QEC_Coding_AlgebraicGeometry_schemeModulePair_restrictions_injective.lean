-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModulePair_restrictions_injective
-- name    : QEC.Coding.AlgebraicGeometry.schemeModulePair_restrictions_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:11.716787+00:00
-- url     : https://prove2.me/theorems/2305d96f-7f8a-47df-9b04-6cc6a45e74fa
-- title:
--   Algebraic Geometry: scheme Module Pair restrictions injective
-- statement:
--   The Algebraic Geometry construction uses the scheme Module Pair restrictions injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ModulePairDescent.lean#L77-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ModulePairDescent.lean#L77-L84

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)

theorem QEC.Coding.AlgebraicGeometry.schemeModulePair_restrictions_injective (hcover : U ⊔ V = ⊤) :
    Function.Injective (fun z : Γ(M, ⊤) =>
      ((M.presheaf.map (homOfLE le_top).op z,
       M.presheaf.map (homOfLE le_top).op z) : Γ(M,U) × Γ(M,V))) := by sorry
