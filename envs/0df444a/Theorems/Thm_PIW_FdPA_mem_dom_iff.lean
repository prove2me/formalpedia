-- Prove2me | Theorems.Thm_PIW_FdPA_mem_dom_iff
-- name    : PIW.FdPA.mem_dom_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:43.05889+00:00
-- url     : https://prove2.me/theorems/c00fe6d5-7570-46c9-9179-3b8947bdbe70
-- title:
--   Fd PA: mem dom iff
-- statement:
--   The Fd PA construction uses the mem dom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/Frames.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/Frames.lean#L10-L12

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

theorem PIW.FdPA.mem_dom_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) : x ∈ X.dom ↔ ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by sorry
