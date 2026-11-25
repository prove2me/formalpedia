-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isLeast_schurComplement___c6fe192388c0
-- name    : P2M_GlobalTheory_isLeast_schurComplement___c6fe192388c0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:02.271712+00:00
-- url     : https://prove2.me/theorems/070688e0-ca3c-5935-88d0-0fb9aae0afff
-- title:
--   P2 M Global Theory is Least schur Complement   c6fe192388c0: P2 M Global Theory is Least schur Complement   c6fe192388c0
-- statement:
--   The P2 M Global Theory is Least schur Complement   c6fe192388c0 construction uses the P2 M Global Theory is Least schur Complement   c6fe192388c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L503-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L503-L523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {m n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m]
omit [DecidableEq n]

theorem P2M_GlobalTheory_isLeast_schurComplement___c6fe192388c0 {G : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : G.PosDef) (v : n → ℂ) :
    IsLeast (range fun u : m → ℂ => (star (Sum.elim u v) ⬝ᵥ G *ᵥ Sum.elim u v).re)
      (star v ⬝ᵥ schurComplement₁₁ G *ᵥ v).re := by sorry

alias «GlobalTheory».«isLeast_schurComplement₁₁» := P2M_GlobalTheory_isLeast_schurComplement___c6fe192388c0
