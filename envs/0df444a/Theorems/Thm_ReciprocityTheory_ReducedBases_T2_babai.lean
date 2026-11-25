-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_babai
-- name    : ReciprocityTheory.ReducedBases.T2.babai
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:33.867964+00:00
-- url     : https://prove2.me/theorems/fa61d282-4150-4520-8a08-97906d2a0bc0
-- title:
--   T2: babai
-- statement:
--   The T2 construction uses the babai property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L79-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L79-L121

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.babai (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (t : ℕ) (ht : t ≤ d) : ∃ w : Fin d → ℤ, (∀ l : Fin d, t ≤ l.val → w l = 0) ∧
      ∀ j : Fin d, j.val < t → |nu b (fun l => c l - N * (w l : ℝ)) j| ≤ N / 2 := by sorry
