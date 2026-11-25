-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_cut
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_cut
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:04.223539+00:00
-- url     : https://prove2.me/theorems/888f060a-b678-5ee7-92f8-906aa66c0153
-- title:
--   Arakelov Geometry: gbap cut
-- statement:
--   The Arakelov Geometry construction uses the gbap cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L146-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStA.lean#L146-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MvPolynomial Module ReciprocityTheory.AnForm.R

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_cut {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) [P.IsPrime]
    (hhor : ∀ m : ℤ, (C m : MvPolynomial J ℤ) ∈ P → m = 0)
    (hdim : ringKrullDim (MvPolynomial J ℤ ⧸ P) = ((D + 1 + 1 : ℕ) : WithBot ℕ∞))
    (z₀ : J → ℂ) (hz₀ : ∀ f ∈ P, eval z₀ (map (Int.castRingHom ℂ) f) = 0)
    (f : Fin c → MvPolynomial J ℤ) (hfP : ∀ i, f i ∈ P)
    (hli : LinearIndependent ℂ
      (fun i => grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e (f i))))) :
    ∃ (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ),
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j)) (F i)) ∧
      eval (fun j => z₀ (e.symm j)) h ≠ 0 ∧
      ∀ w : Fin (D + 1 + c) → ℂ, eval w h ≠ 0 →
        ((∀ i, eval w (F i) = 0) ↔
          ∀ g ∈ P, eval (fun j => w (e j)) (map (Int.castRingHom ℂ) g) = 0) := by sorry
