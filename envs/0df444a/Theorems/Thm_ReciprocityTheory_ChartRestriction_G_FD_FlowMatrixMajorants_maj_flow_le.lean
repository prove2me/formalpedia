-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_maj_flow_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.maj_flow_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:39.126044+00:00
-- url     : https://prove2.me/theorems/f2370284-6b90-4ee5-b775-26227f0e36ed
-- title:
--   Flow Matrix Majorants: maj flow le
-- statement:
--   The Flow Matrix Majorants construction uses the maj flow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatrixMajorants.lean#L212-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatrixMajorants.lean#L212-L305

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.maj_flow_le {x : Frame X.Ψ r} (hx : x ∈ X.dom) (t : ℝ) (u : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) ≤
      (1 + X.c τ * |t| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ u := by sorry
