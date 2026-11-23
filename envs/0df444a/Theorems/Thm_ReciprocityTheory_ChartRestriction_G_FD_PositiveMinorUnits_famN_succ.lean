-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_famN_succ
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.famN_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:46.917873+00:00
-- url     : https://prove2.me/theorems/db9dde82-37b6-4402-b70b-0b7376c8850c
-- title:
--   Positive Minor Units: fam N succ
-- statement:
--   The Positive Minor Units construction uses the fam N succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveMinorUnits.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveMinorUnits.lean#L19-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

theorem ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.famN_succ (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (h : i + 1 ≤ r) :
    (fun a : Fin i => famN x (i + 1) h a.castSucc) = famN x i (Nat.le_of_succ_le h) := by sorry
