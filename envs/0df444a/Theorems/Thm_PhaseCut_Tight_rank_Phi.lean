-- Prove2me | Theorems.Thm_PhaseCut_Tight_rank_Phi
-- name    : PhaseCut.Tight.rank_Phi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:19.53698+00:00
-- url     : https://prove2.me/theorems/8fe6e6fa-2c36-4195-b847-2760a96abb8d
-- title:
--   Proof of Corollary 4.3, p. 13 — for injective A and bᵢ ≠ 0, Rank(X) = Rank(Φ(X))
-- statement:
--   Let $A\in\mathbb C^{n\times p}$ be injective and let $b\in\mathbb R^n$ with $b_i\neq 0$ for all $i$. With $\Phi(X)=\operatorname{diag}(b)^{-1}AXA^*\operatorname{diag}(b)^{-1}$, every $X\in\mathbb C^{p\times p}$ satisfies
--
--   $$\operatorname{Rank}(X)=\operatorname{Rank}\bigl(\Phi(X)\bigr).$$
--
--   So $\Phi$ maps rank-one matrices exactly to rank-one matrices, which is what lets tightness ("a unique rank one solution") pass from PhaseLift to PhaseCutMod.
--
--   **Formalization Note** Rank is Mathlib's `Matrix.rank` over $\mathbb C$.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Corollary 4.3, p. 13

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- Proof of Corollary 4.3, p. 13: for injective `A` and `bᵢ ≠ 0`, `Rank(X) = Rank(Φ(X))` for every
`p × p` complex matrix `X`. -/
theorem rank_Phi {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) :
    ∀ X : Matrix (Fin p) (Fin p) ℂ, X.rank = (Phi A b X).rank := by sorry

end PhaseCut.Tight
