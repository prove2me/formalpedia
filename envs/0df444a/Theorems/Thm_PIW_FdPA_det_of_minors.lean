-- Prove2me | Theorems.Thm_PIW_FdPA_det_of_minors
-- name    : PIW.FdPA.det_of_minors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:46.513418+00:00
-- url     : https://prove2.me/theorems/89227f7c-0f14-499f-9b2f-e283bd958e63
-- title:
--   Fd PA: det of minors
-- statement:
--   The Fd PA construction uses the det of minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/Frames.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/Frames.lean#L32-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section

theorem PIW.FdPA.det_of_minors {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (τ : X.Ψ) (h : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re) :
    (mat x τ).det ≠ 0 := by sorry
