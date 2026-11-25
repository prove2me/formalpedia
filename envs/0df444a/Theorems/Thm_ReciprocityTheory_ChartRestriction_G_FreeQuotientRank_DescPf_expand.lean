-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_expand
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.expand
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:20.822543+00:00
-- url     : https://prove2.me/theorems/69d0139a-c62a-48fe-ae8c-41861f054efd
-- title:
--   Desc Pf: expand
-- statement:
--   The Desc Pf construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L34-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L34-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.expand [FiniteDimensional K K₂] [Algebra.IsSeparable K K₂] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K K₂) (w : K₂ ⊗[K] V) :
    w = ∑ i, ((Algebra.traceForm K K₂).dualBasis
      (traceForm_nondegenerate (K := K) (L := K₂)) b i) • ((1 : K₂) ⊗ₜ[K] trT (b i • w)) := by sorry
