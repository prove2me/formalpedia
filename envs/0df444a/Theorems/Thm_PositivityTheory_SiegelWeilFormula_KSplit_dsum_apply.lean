-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dsum_apply
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.dsum_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:43.668206+00:00
-- url     : https://prove2.me/theorems/21c849cf-f154-4723-afd7-7520e9da2832
-- title:
--   KSplit: dsum apply
-- statement:
--   The KSplit construction uses the dsum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L281-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L281-L286

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.SiegelWeilFormula.KSplit.dsum_apply {ι : Type} (s : Finset ι) (D : ι → Derivation ℂ (PX m n) (PX m n)) (P : PX m n) :
    (∑ i ∈ s, D i) P = ∑ i ∈ s, D i P := by sorry
