-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single__5657c32646f4
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single__5657c32646f4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:13.363197+00:00
-- url     : https://prove2.me/theorems/e44030f7-0366-4370-be4f-ef0a0530d0f7
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 KAV d Add single  5657c32646f4: P2 M Formalism Main Notions Moduli Integral Charts H1 KAV d Add single  5657c32646f4
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 KAV d Add single  5657c32646f4 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 KAV d Add single  5657c32646f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L82-L84

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single__5657c32646f4 {S : Type} [CommRing S] {d n : ℕ} (j : Fin d) (b : Fin n) :
    (TB.dAdd (Pi.single j 1) b : Germ.PS S n d → Germ.PS S n d) = pderiv S (b, j) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«KAV».«dAdd_single'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single__5657c32646f4
