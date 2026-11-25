-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartPrimTrPf_prim__comm_976fe62e9077
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartPrimTrPf_prim__comm_976fe62e9077
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:40.637286+00:00
-- url     : https://prove2.me/theorems/8e629332-afdc-431c-8a5f-3b8fd705320d
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Chart Prim Tr Pf prim  comm 976fe62e9077: P2 M Formalism Main Notions Moduli Integral Charts H1 Chart Prim Tr Pf prim  comm 976fe62e9077
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Chart Prim Tr Pf prim  comm 976fe62e9077 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Chart Prim Tr Pf prim  comm 976fe62e9077 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartPrimTrPfA.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartPrimTrPfA.lean#L18-L29

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrPfA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartPrimTrPf_prim__comm_976fe62e9077 {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) : primφ t' k ≫ m.φ = m.φ ≫ primφ t k := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ChartPrimTrPf».«primφ_comm» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartPrimTrPf_prim__comm_976fe62e9077
