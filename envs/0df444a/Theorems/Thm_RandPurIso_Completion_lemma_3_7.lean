-- Prove2me | Theorems.Thm_RandPurIso_Completion_lemma_3_7
-- name    : RandPurIso.Completion.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:12.693198+00:00
-- url     : https://prove2.me/theorems/b9533df7-493c-40e3-b2f3-363153fef21d
-- title:
--   Lemma 3.7 — operator-norm facts for partial isometries
-- statement:
--   Let $V_1,V_2,W_1,W_2$ be partial isometries. Then
--
--   1. $\|V_1W_1-V_2W_2\|_{op}\le\|V_1-V_2\|_{op}+\|W_1-W_2\|_{op}$ (for composable $V_i:B\to C$, $W_i:A\to B$);
--   2. $\|(V_1+V_2)-(W_1+W_2)\|_{op}\le\|V_1-W_1\|_{op}+\|V_2-W_2\|_{op}$ (all of one shape);
--   3. $\|V_1\|_{op}=\|V_1^\dagger\|_{op}$.
--
--   Differences from the source:
--   - encoding: one list of four partial isometries → each clause quantified over the shapes that make it well typed; reason: the clauses need different shapes; no instance changes
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 3.7, p. 19

import Mathlib
import Definitions.Def_RandPurIso_Completion_IsContraction
import Definitions.Def_RandPurIso_Completion_opNorm
open Matrix

namespace RandPurIso.Completion

/-- **Lemma 3.7** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 19). Let `V₁, V₂, W₁, W₂` be partial isometries. Then
`‖V₁W₁ − V₂W₂‖_op ≤ ‖V₁ − V₂‖_op + ‖W₁ − W₂‖_op`,
`‖(V₁ + V₂) − (W₁ + W₂)‖_op ≤ ‖V₁ − W₁‖_op + ‖V₂ − W₂‖_op`, and `‖V₁‖_op = ‖V₁†‖_op`.

**Formalization Note.** All three clauses; each is stated for the shapes that make it well typed
(composable `V_i : Y → Z`, `W_i : X → Y` in the first; one common shape in the second). -/
theorem lemma_3_7 :
    (∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
      (V1 V2 : Matrix Z Y ℂ) (W1 W2 : Matrix Y X ℂ),
      IsPartialIsometry V1 → IsPartialIsometry V2 → IsPartialIsometry W1 → IsPartialIsometry W2 →
      opNorm (V1 * W1 - V2 * W2) ≤ opNorm (V1 - V2) + opNorm (W1 - W2)) ∧
    (∀ {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
      (V1 V2 W1 W2 : Matrix Y X ℂ),
      IsPartialIsometry V1 → IsPartialIsometry V2 → IsPartialIsometry W1 → IsPartialIsometry W2 →
      opNorm ((V1 + V2) - (W1 + W2)) ≤ opNorm (V1 - W1) + opNorm (V2 - W2)) ∧
    (∀ {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (V1 : Matrix Y X ℂ), IsPartialIsometry V1 → opNorm V1 = opNorm V1ᴴ) := by sorry

end RandPurIso.Completion
