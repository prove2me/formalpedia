-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_example_schurQuotientPeriod_hyp_644af350108a
-- name    : P2M_GroundTheory_Heights__Heights_example_schurQuotientPeriod_hyp_644af350108a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:07.316295+00:00
-- url     : https://prove2.me/theorems/17d2ebcf-b53f-429a-9105-cea3956fc4d3
-- title:
--   P2 M Ground Theory Heights  Heights example schur Quotient Period hyp 644af350108a: P2 M Ground Theory Heights  Heights example schur Quotient Period hyp 644af350108a
-- statement:
--   The P2 M Ground Theory Heights  Heights example schur Quotient Period hyp 644af350108a construction uses the P2 M Ground Theory Heights  Heights example schur Quotient Period hyp 644af350108a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Statements.lean#L284-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Statements.lean#L284-L290

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
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

theorem P2M_GroundTheory_Heights__Heights_example_schurQuotientPeriod_hyp_644af350108a :
    let τ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
      Matrix.diagonal (Sum.elim (fun _ => Complex.I) (fun _ => 1 + 2 * Complex.I))
    τᵀ = τ ∧ (τ.map Complex.im).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«example_schurQuotientPeriod_hyp» := P2M_GroundTheory_Heights__Heights_example_schurQuotientPeriod_hyp_644af350108a
