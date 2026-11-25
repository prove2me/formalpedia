-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_star_exp_mul_I
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.star_exp_mul_I
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:51.177184+00:00
-- url     : https://prove2.me/theorems/f019efeb-197f-48ef-a845-210d8edcc3d5
-- title:
--   KSplit: star exp mul I
-- statement:
--   The KSplit construction uses the star exp mul I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L183-L186

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.star_exp_mul_I (t : ℝ) : star (Complex.exp (t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by sorry
