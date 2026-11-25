-- Prove2me | Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_bmA_prod_update_zero__a3a3001d3055
-- name    : P2M_Formalism_BranchingDeterminantCap_bmA_prod_update_zero__a3a3001d3055
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:40.689549+00:00
-- url     : https://prove2.me/theorems/203ea3a5-328a-4061-84fa-42b1f92e3e81
-- title:
--   P2 M Formalism Branching Determinant Cap bm A prod update zero  a3a3001d3055: P2 M Formalism Branching Determinant Cap bm A prod update zero  a3a3001d3055
-- statement:
--   The P2 M Formalism Branching Determinant Cap bm A prod update zero  a3a3001d3055 construction uses the P2 M Formalism Branching Determinant Cap bm A prod update zero  a3a3001d3055 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L581-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L581-L585

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {A : Type*} [Ring A]

theorem P2M_Formalism_BranchingDeterminantCap_bmA_prod_update_zero__a3a3001d3055 {n : ℕ} (g : Fin n → A) (k : Fin n) :
    (List.ofFn (Function.update g k 0)).prod = 0 := by sorry

alias «Formalism».«BranchingDeterminantCap».«bmA_prod_update_zero'» := P2M_Formalism_BranchingDeterminantCap_bmA_prod_update_zero__a3a3001d3055
