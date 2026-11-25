-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_length_quot
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.length_quot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:39.906479+00:00
-- url     : https://prove2.me/theorems/692139d9-e168-4dbc-8c9c-d685214300b7
-- title:
--   HDisc Lat: length quot
-- statement:
--   The HDisc Lat construction uses the length quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAA.lean#L60-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAA.lean#L60-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.length_quot {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    {CC V : Type*} [AddCommGroup CC] [Module R CC] [AddCommGroup V] [Module R V]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (α : Basis κ R CC) (φ : CC →ₗ[R] V)
    (hφ : Function.Injective φ) (SA : Submodule R V) (hSA : SA = LinearMap.range φ)
    {m : ℕ} (b' : Fin m → CC) (hli : LinearIndependent R b') (σ : κ ≃ Fin m) :
    ∃ n : ℕ, ∃ u : Rˣ,
      Module.length R (SA ⧸ (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype) = n ∧
      α.det (b' ∘ σ) = u * ϖ ^ n := by sorry
