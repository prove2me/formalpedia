-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Frob_pull_pull_symm
-- name    : PositivityTheory.PfBern.Frob.pull_pull_symm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:50.558445+00:00
-- url     : https://prove2.me/theorems/bdeb1904-bb38-5392-9cd9-2cd79d94178b
-- title:
--   Frob: pull pull symm
-- statement:
--   The Frob construction uses the pull pull symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/FrobProof.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/FrobProof.lean#L18-L20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob

theorem PositivityTheory.PfBern.Frob.pull_pull_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (F : SB Y) : pullHomeo e.symm (pullHomeo e F) = F := by sorry
