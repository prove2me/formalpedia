-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModulePair_existsUnique_global
-- name    : QEC.Coding.AlgebraicGeometry.schemeModulePair_existsUnique_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:01:17.128203+00:00
-- url     : https://prove2.me/theorems/b60f3a67-1a1e-4c1c-a3e0-4258c9e65aa0
-- title:
--   Algebraic Geometry: scheme Module Pair exists Unique global
-- statement:
--   The Algebraic Geometry construction uses the scheme Module Pair exists Unique global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ModulePairDescent.lean#L59-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ModulePairDescent.lean#L59-L75

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

theorem QEC.Coding.AlgebraicGeometry.schemeModulePair_existsUnique_global (hcover : U ⊔ V = ⊤)
    (s : Γ(M, U)) (t : Γ(M, V))
    (h : M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s =
      M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t) :
    ∃! z : Γ(M, ⊤), M.presheaf.map (homOfLE le_top).op z = s ∧
      M.presheaf.map (homOfLE le_top).op z = t := by sorry
