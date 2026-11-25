-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_UnimodularLast_exists_basis_d879db4ccda8
-- name    : P2M_GroundTheory_Heights__Heights_UnimodularLast_exists_basis_d879db4ccda8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:01.178064+00:00
-- url     : https://prove2.me/theorems/88530bc3-0286-50f7-9787-5bbcf35dc8c0
-- title:
--   P2 M Ground Theory Heights  Heights Unimodular Last exists basis d879db4ccda8: P2 M Ground Theory Heights  Heights Unimodular Last exists basis d879db4ccda8
-- statement:
--   The P2 M Ground Theory Heights  Heights Unimodular Last exists basis d879db4ccda8 construction uses the P2 M Ground Theory Heights  Heights Unimodular Last exists basis d879db4ccda8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PUnimodularLast.lean#L20-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PUnimodularLast.lean#L20-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PUnimodularLast
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
open GroundTheory.Heights₂.Heights.UnimodularLast

theorem P2M_GroundTheory_Heights__Heights_UnimodularLast_exists_basis_d879db4ccda8 (k : ℕ) (ρ : Fin (k + 1) → ℤ) (hρ : ρ ≠ 0) :
    ∃ b : Module.Basis (Fin (k + 1)) ℤ (Fin (k + 1) → ℤ),
      (∀ j : Fin k, ρ ⬝ᵥ b (Fin.castSucc j) = 0) ∧ ρ ⬝ᵥ b (Fin.last k) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«UnimodularLast».«exists_basis» := P2M_GroundTheory_Heights__Heights_UnimodularLast_exists_basis_d879db4ccda8
