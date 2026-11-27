-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_sum_split__579f930c6f43
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_sum_split__579f930c6f43
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:42.943484+00:00
-- url     : https://prove2.me/theorems/f5311a8d-2347-478a-8440-cfd25bc58cd8
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis sum split  579f930c6f43: P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis sum split  579f930c6f43
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis sum split  579f930c6f43 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Perp Basis sum split  579f930c6f43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L16-L32

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_sum_split__579f930c6f43 {M : Type*} [AddCommMonoid M] (f : Fin r → M) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«OrthonormalPerpBasis».«sum_split'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_sum_split__579f930c6f43
