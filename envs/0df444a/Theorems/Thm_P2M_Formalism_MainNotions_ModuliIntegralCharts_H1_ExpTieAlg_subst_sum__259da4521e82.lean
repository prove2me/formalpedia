-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sum__259da4521e82
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sum__259da4521e82
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:04.255009+00:00
-- url     : https://prove2.me/theorems/07c40f7c-82a1-4f1b-a5d8-ea9b918ce3dd
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Alg subst sum  259da4521e82: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Alg subst sum  259da4521e82
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Alg subst sum  259da4521e82 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Alg subst sum  259da4521e82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L90-L96

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sum__259da4521e82 {σ τ : Type} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) {ι : Type} (s : Finset ι)
    (g : ι → MvPowerSeries σ S) : subst a (∑ i ∈ s, g i) = ∑ i ∈ s, subst a (g i) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpTieAlg».«subst_sum'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sum__259da4521e82
