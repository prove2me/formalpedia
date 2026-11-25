-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_hC_sum_right__1bac482c7394
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_hC_sum_right__1bac482c7394
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:50.022072+00:00
-- url     : https://prove2.me/theorems/9dae7b48-b14a-4e4c-9234-c341c1ccf351
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis h C sum right  1bac482c7394: P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis h C sum right  1bac482c7394
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis h C sum right  1bac482c7394 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis h C sum right  1bac482c7394 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L34-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_hC_sum_right__1bac482c7394 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«OrthonormalPerpBasis».«hC_sum_right'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_hC_sum_right__1bac482c7394
