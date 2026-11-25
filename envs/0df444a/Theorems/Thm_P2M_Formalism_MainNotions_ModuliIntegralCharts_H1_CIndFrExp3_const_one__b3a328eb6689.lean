-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_const_one__b3a328eb6689
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_const_one__b3a328eb6689
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:22:29.607655+00:00
-- url     : https://prove2.me/theorems/6ffd7518-8d62-4118-ac12-41458601ad9b
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp3 const one  b3a328eb6689: P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp3 const one  b3a328eb6689
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp3 const one  b3a328eb6689 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp3 const one  b3a328eb6689 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L94-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L94-L136

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_const_one__b3a328eb6689 {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hfF : ∀ i, fF i ∈ Io S (Fin 3 × Fin d))
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«CIndFrExp3».«const_one'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_const_one__b3a328eb6689
