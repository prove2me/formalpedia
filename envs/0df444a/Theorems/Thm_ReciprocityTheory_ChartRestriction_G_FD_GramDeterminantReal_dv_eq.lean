-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.dv_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:17.541241+00:00
-- url     : https://prove2.me/theorems/54e799d3-7029-4236-a5b7-3cb61f6c7a49
-- title:
--   Gram Determinant Real: dv eq
-- statement:
--   The Gram Determinant Real construction uses the dv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L79-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.dv_eq {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ) :
    dv τ G f e = ∑ b, (yv τ G f e b -
      Fin.snoc (α := fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b) • f b := by sorry
