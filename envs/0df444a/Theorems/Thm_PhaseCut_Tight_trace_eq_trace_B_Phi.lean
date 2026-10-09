-- Prove2me | Theorems.Thm_PhaseCut_Tight_trace_eq_trace_B_Phi
-- name    : PhaseCut.Tight.trace_eq_trace_B_Phi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:06.708613+00:00
-- url     : https://prove2.me/theorems/3080f4d8-a162-469a-8392-2b3a424e9980
-- title:
--   Proof of Corollary 4.3, p. 13 — for injective A and bᵢ ≠ 0, Tr(X) = Tr(BΦ(X))
-- statement:
--   Let $A\in\mathbb C^{n\times p}$ be injective with pseudoinverse $A^\dagger=(A^*A)^{-1}A^*$, and let $b\in\mathbb R^n$ with $b_i\neq 0$ for all $i$. With $B=\operatorname{diag}(b)A^{\dagger *}A^\dagger\operatorname{diag}(b)$ and $\Phi(X)=\operatorname{diag}(b)^{-1}AXA^*\operatorname{diag}(b)^{-1}$, every $X\in\mathbb C^{p\times p}$ satisfies
--
--   $$\operatorname{Tr}(X)=\operatorname{Tr}\bigl(B\,\Phi(X)\bigr).$$
--
--   So $\Phi$ carries the PhaseLift objective to the PhaseCutMod objective; together with Proposition 4.2 it identifies the optimal sets of the two programs.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Corollary 4.3, p. 13

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- Proof of Corollary 4.3, p. 13: for injective `A` and `bᵢ ≠ 0`, `Tr(X) = Tr(BΦ(X))` for every
`p × p` complex matrix `X`. -/
theorem trace_eq_trace_B_Phi {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) :
    ∀ X : Matrix (Fin p) (Fin p) ℂ, X.trace = (Bmat A b * Phi A b X).trace := by sorry

end PhaseCut.Tight
