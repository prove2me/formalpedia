-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_lemma4
-- name    : SongZipkinFluct.Linear.lemma4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:29.957455+00:00
-- url     : https://prove2.me/theorems/5f77ac98-900c-4f37-9b1f-9259d8af21eb
-- title:
--   Lemma 4 — uniform finite bounds on Wₙ
-- statement:
--   Suppose the terminal transformed cost $W_0$ lies between zero and a finite nondecreasing bound $W_0^B(x)$ for every world state. Then a finite nondecreasing function $W^B(x)$ bounds every later stage cost uniformly in the world state and stage number:
--
--   $$0\le W_0(i,x)\le W_0^B(x)\quad\Longrightarrow\quad 0\le W_n(i,x)\le W^B(x)\qquad(n\ge1).$$
--
--   This bound keeps the infinite-state continuation sums finite. The model's discounted fixed cost $K$ is used in the recursion.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 356, Lemma 4, (11)–(12)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Lemma 4, p. 356, displays (11)--(12).
Here `K=M.K` is the model's discounted fixed order cost. The hypothesis
on `W₀` is exactly (11), and no summability of the recursion is assumed. -/
theorem lemma4 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1)
    (W₀ : I → ℤ → ℝ)
    (WBound₀ : ℤ → ℝ) (hmono₀ : Monotone WBound₀)
    (hbound₀ : ∀ i x, 0 ≤ W₀ i x ∧ W₀ i x ≤ WBound₀ x) :
    ∃ WBound : ℤ → ℝ, Monotone WBound ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i x, 0 ≤ M.W M.K W₀ n i x ∧
        M.W M.K W₀ n i x ≤ WBound x := by sorry

end SongZipkinFluct.Linear
