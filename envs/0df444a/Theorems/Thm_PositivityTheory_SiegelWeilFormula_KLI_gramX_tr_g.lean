-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_gramX_tr_g
-- name    : PositivityTheory.SiegelWeilFormula.KLI.gramX_tr_g
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:15.870548+00:00
-- url     : https://prove2.me/theorems/ba76a1e0-2370-468f-a955-878f8bed3216
-- title:
--   KLI: gram X tr g
-- statement:
--   The KLI construction uses the gram X tr g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussSec.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussSec.lean#L13-L16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix PositivityTheory.Rg.Sw
open scoped Matrix ComplexConjugate
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
variable {m n : ℕ}

theorem PositivityTheory.SiegelWeilFormula.KLI.gramX_tr_g (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX (fun _ : Fin m => true) x j i = ∑ a, star (x a j) * x a i := by sorry
