-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_subst__b3c6c3b879e6
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_subst__b3c6c3b879e6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:35.655812+00:00
-- url     : https://prove2.me/theorems/b74c777e-8987-416d-856f-b93a1a2d8705
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp2a low subst  b3c6c3b879e6: P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp2a low subst  b3c6c3b879e6
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp2a low subst  b3c6c3b879e6 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Exp2a low subst  b3c6c3b879e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LogLowOrderOne.lean#L23-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LogLowOrderOne.lean#L23-L44

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_subst__b3c6c3b879e6 {ι τ : Type} [Finite ι] {N : ℕ} {k : ι → MvPowerSeries τ S} (hk : ∀ i, Low 1 (k i))
    {g : MvPowerSeries ι S} (hg : Low N g) : Low N (subst k g) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«CIndFrExp2a».«low_subst'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_subst__b3c6c3b879e6
