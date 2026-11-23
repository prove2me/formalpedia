-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_majorant_realFlow_transfer
-- name    : ReciprocityTheory.ChartRestriction.G.FD.majorant_realFlow_transfer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:56.743707+00:00
-- url     : https://prove2.me/theorems/2462b4a6-398b-43e1-94ea-4368609cefea
-- title:
--   FD: majorant real Flow transfer
-- statement:
--   The FD construction uses the majorant real Flow transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMinimumLowerBoundHolds.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMinimumLowerBoundHolds.lean#L12-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.majorant_realFlow_transfer {r : ℕ} (X : Data E r) (ξ : Fin r → E) (t : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hz : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom) (τ : X.Ψ)
    (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => (t τ : ℂ)) x) τ w =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-(t τ : ℂ))) w) := by sorry
