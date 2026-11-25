-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_hermValue_single_36ddafe20269
-- name    : P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_hermValue_single_36ddafe20269
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:39.300083+00:00
-- url     : https://prove2.me/theorems/bd85a965-2787-43b5-bcc2-0e701a44a38f
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Leading Minima herm Value single 36ddafe20269: P2 M Ground Theory Heights  Heights Cusp Leading Minima herm Value single 36ddafe20269
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Leading Minima herm Value single 36ddafe20269 construction uses the P2 M Ground Theory Heights  Heights Cusp Leading Minima herm Value single 36ddafe20269 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspLeadingMinima.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspLeadingMinima.lean#L39-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLeadingMinima
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.CuspLeadingMinima

theorem P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_hermValue_single_36ddafe20269 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (k : ι) :
    hermValue A (Pi.single k (1 : ℂ)) = A k k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspLeadingMinima».«hermValue_single» := P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_hermValue_single_36ddafe20269
