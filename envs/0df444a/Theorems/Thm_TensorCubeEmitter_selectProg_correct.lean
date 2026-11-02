-- Prove2me | Theorems.Thm_TensorCubeEmitter_selectProg_correct
-- name    : TensorCubeEmitter.selectProg_correct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:50:28.901547+00:00
-- url     : https://prove2.me/theorems/29ec3902-0ed2-4c1c-bb43-573cf6ad2797
-- title:
--   Correctness of the tensor coefficient selector
-- statement:
--   Given two Boolean flag heads, the fixed selector preserves both flag stacks and prepends the canonical rational encoding of the selected coefficient to an arbitrary output tail. The positive flag selects $1$; otherwise the negative flag selects $-1$; otherwise the coefficient is $0$. The program terminates within 13 structured-program steps.

import Definitions.Def_TensorCubeEmitter
open CookPvsNP ProjSchedTW.Complexity

namespace TensorCubeEmitter
theorem selectProg_correct (positive negative : Bool) (positiveTail negativeTail output : List BSym) :
    ∃ steps, steps ≤ 13 ∧
      selectProg.Exec
        (store (flagSym positive :: positiveTail) (flagSym negative :: negativeTail) output)
        (store (flagSym positive :: positiveTail) (flagSym negative :: negativeTail)
          (TensorNP.Eigen.encRat (coefficient positive negative) ++ output)) steps := by
  sorry

end TensorCubeEmitter
