-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_zbas_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.zbas_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:53.889154+00:00
-- url     : https://prove2.me/theorems/21f5bcea-c01c-5e4f-a28e-c3ca4978883a
-- title:
--   Integral Basis Reduction: zbas apply
-- statement:
--   The Integral Basis Reduction construction uses the zbas apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralBasisReduction.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralBasisReduction.lean#L84-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.zbas_apply {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ)
    (i : ι) : zbas X hy g i = Ly X y (X.embV (g i : Fin r → E)) := by sorry
