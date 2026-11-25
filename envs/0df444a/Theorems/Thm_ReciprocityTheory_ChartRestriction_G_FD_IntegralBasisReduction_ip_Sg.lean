-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_ip_Sg
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.ip_Sg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:56.214039+00:00
-- url     : https://prove2.me/theorems/083b4401-1790-5ea4-ba53-059e725692a5
-- title:
--   Integral Basis Reduction: ip Sg
-- statement:
--   The Integral Basis Reduction construction uses the ip Sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralBasisReduction.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralBasisReduction.lean#L59-L74

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

theorem ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.ip_Sg {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (p q : Fin r → E) :
    ip X (Ly X y (X.embV p)) (Sg X (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm X.Gm p q)).re := by sorry
