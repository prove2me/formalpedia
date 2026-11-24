-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_colon_chain
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_colon_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:01.061717+00:00
-- url     : https://prove2.me/theorems/cf632ea2-f415-4c00-83a7-921f13d19e5b
-- title:
--   Arakelov Geometry: le colon chain
-- statement:
--   The Arakelov Geometry construction uses the le colon chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/MultAtEqCount.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/MultAtEqCount.lean#L11-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_MultAtEqCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_colon_chain {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) (j : Fin N) : J ≤ q j := by sorry
