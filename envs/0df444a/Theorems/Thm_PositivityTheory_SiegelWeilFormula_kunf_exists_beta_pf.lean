-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_kunf_exists_beta_pf
-- name    : PositivityTheory.SiegelWeilFormula.kunf.exists_beta_pf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:54.809999+00:00
-- url     : https://prove2.me/theorems/1124168e-f69a-4b61-98e1-3c3330066cb8
-- title:
--   kunf: exists beta pf
-- statement:
--   The kunf construction uses the exists beta pf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/ExistsBetaPf.lean#L7-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/ExistsBetaPf.lean#L7-L66

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_ExistsBetaPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.kunf

theorem PositivityTheory.SiegelWeilFormula.kunf.exists_beta_pf {K : Type} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : K) (he : e * e = 1)
    (hse : s e = e) (a c d' : Matrix (Fin n) (Fin n) K) (hc : c.det = 0) (hda : e • (c.map s)ᵀ * a + d' * c = 0)
    (T : Matrix (Fin n) (Fin n) K) (hT : Tᵀ = -(e • T.map s)) (hTd : T.det ≠ 0) :
    ∃ β₁ : Matrix (Fin n) (Fin n) K, β₁ᵀ = -(e • β₁.map s) ∧ c * β₁ * (e • (c.map s)ᵀ) = 0 ∧
      (∃ v w : Fin n → K, a * β₁ * (e • (c.map s)ᵀ) = Matrix.vecMulVec v w ∧ w ⬝ᵥ v = 0) ∧ (T * β₁).trace = 2 := by sorry
