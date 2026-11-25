-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_exists_det_submatrix_ne_zero_613386e27c04
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_exists_det_submatrix_ne_zero_613386e27c04
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:08.909702+00:00
-- url     : https://prove2.me/theorems/033ee5ff-a633-4fe1-9755-662f62a6e7a7
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Zero Locus exists det submatrix ne zero 613386e27c04: P2 M Ground Theory Heights  Heights Incidence Zero Locus exists det submatrix ne zero 613386e27c04
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Zero Locus exists det submatrix ne zero 613386e27c04 construction uses the P2 M Ground Theory Heights  Heights Incidence Zero Locus exists det submatrix ne zero 613386e27c04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L13-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus

theorem P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_exists_det_submatrix_ne_zero_613386e27c04 {K ρ κ : Type*} [Field K] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] (A : Matrix ρ κ K)
    (hA : ∀ f, Pi.single f 1 ∈ Submodule.span K (Set.range A.col)) :
    ∃ e : ρ → κ, (A.submatrix id e).det ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceZeroLocus».«exists_det_submatrix_ne_zero» := P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_exists_det_submatrix_ne_zero_613386e27c04
