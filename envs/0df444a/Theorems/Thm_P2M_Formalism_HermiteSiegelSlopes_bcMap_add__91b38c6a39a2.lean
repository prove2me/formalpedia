-- Prove2me | Theorems.Thm_P2M_Formalism_HermiteSiegelSlopes_bcMap_add__91b38c6a39a2
-- name    : P2M_Formalism_HermiteSiegelSlopes_bcMap_add__91b38c6a39a2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:28.135782+00:00
-- url     : https://prove2.me/theorems/4d321450-5089-4b23-a383-e223f10a1b9c
-- title:
--   P2 M Formalism Hermite Siegel Slopes bc Map add  91b38c6a39a2: P2 M Formalism Hermite Siegel Slopes bc Map add  91b38c6a39a2
-- statement:
--   The P2 M Formalism Hermite Siegel Slopes bc Map add  91b38c6a39a2 construction uses the P2 M Formalism Hermite Siegel Slopes bc Map add  91b38c6a39a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L266-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L266-L268

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]

theorem P2M_Formalism_HermiteSiegelSlopes_bcMap_add__91b38c6a39a2 (x y : ι → F) : bcMap (E := E) (x + y) = bcMap x + bcMap y := by sorry

alias «Formalism».«HermiteSiegelSlopes».«bcMap_add'» := P2M_Formalism_HermiteSiegelSlopes_bcMap_add__91b38c6a39a2
