-- Prove2me | Theorems.Thm_Pr6453_replay_linear
-- name    : Pr6453.replay_linear
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T22:17:40.335033+00:00
-- url     : https://prove2.me/theorems/a91c74bf-bd3b-4ade-b12b-dba5190a595a
-- title:
--   PR #6453: the rows are a linear function of the input rows
-- statement:
--   The rows a word computes are a linear function of the rows it starts from.
--
--   Run the same program twice from the same frame chart, once with rows $a$ and once with rows $b$. Then it also runs with rows $a+b$, ends at the same frame chart, and its rows are the sums of the two runs' rows. So the output of a word is a linear map applied to its input — which is what a straight-line program over rows is, but stated as a theorem about the replay rather than assumed of the construction.
--
--   This is the output half of the replay in its structural form: the frames half says when the program is legal (each column's own track), the rows half says what it computes (a linear functional of the initial rows). The further step — that the linear map is multiplication of the two input words — is the module semantics of the construction, and it is not part of this statement.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

import Definitions.Def_Pr6453_Replay
import Definitions.Def_Pr6453_Linear

set_option autoImplicit false

namespace Pr6453

theorem replay_linear {n : ℕ} (p : List (Event n)) (fr : Fin n → Option ℕ)
    (a b : Fin n → ℕ →₀ ℚ) (s₁ s₂ : State n)
    (h₁ : replay? p ⟨a, fr⟩ = some s₁) (h₂ : replay? p ⟨b, fr⟩ = some s₂) :
    ∃ s₃ : State n, replay? p ⟨a + b, fr⟩ = some s₃ ∧ s₃.frames = s₁.frames ∧
      ∀ i, s₃.rows i = s₁.rows i + s₂.rows i := by
  sorry

end Pr6453
