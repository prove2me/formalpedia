-- Prove2me | Theorems.Thm_VBSDP_Duality_Supplement_theorem_4_1
-- name    : VBSDP.Duality.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:07:50.852607+00:00
-- url     : https://prove2.me/theorems/60d4c8f3-cac2-4ec1-85ee-d844b4c4073e
-- title:
--   Theorem 4.1 — Newton's method with exact line search reaches ϕ(x⁽ᵏ⁾) − ϕ(x⋆) ≤ ε once k ≥ 11(ϕ(x⁽⁰⁾) − ϕ(x⋆)) + log₂ log₂(1/ε)
-- statement:
--   Let $F_0,\dots,F_m$ be symmetric $n\times n$ real matrices, $F(x)=F_0+\sum_{i=1}^mx_iF_i$, and $\phi(x)=\log\det F(x)^{-1}$ the logarithmic barrier (42) of $\mathbf X=\{x\mid F(x)>0\}$. Assume $\mathbf X$ is bounded (the assumption of §§4.2–4.3), and let $x^\star$ be the analytic center (46), the minimizer of $\phi$. Let $x^{(0)},x^{(1)},\dots$ be the iterates of the Newton method for computing the analytic center (p. 72): $x^{(0)}\in\mathbf X$, and $x^{(k+1)}=x^{(k)}+\hat p\,\delta x^N$ with $\delta x^N$ the Newton direction (48) at $x^{(k)}$ and $\hat p$ an exact line-search minimizer of $\phi(x^{(k)}+p\,\delta x^N)$. Let $0<\epsilon\le0.5$. Then for every
--
--   $$k\ \ge\ 11\big(\phi(x^{(0)})-\phi(x^\star)\big)+\log_2\log_2\Big(\frac1\epsilon\Big)$$
--
--   we have $\phi(x^{(k)})-\phi(x^\star)\le\epsilon$.
--
--   The bound does not depend on the problem size $m$ or $n$, only on the initial barrier gap. The paper refers to Nesterov and Nemirovsky [76, §2.2] for the analysis.
--
--   **Formalization Note** $\phi$ is `barrier`, real-valued, and is only evaluated at points of $\mathbf X$ (the iterates and $x^\star$). The analytic center is given by its minimizing property (`IsAnalyticCenter`); it exists and is unique when $\mathbf X$ is nonempty and bounded. Boundedness of $\mathbf X$ is `Bornology.IsBounded`. $\log_2$ is `Real.logb 2`; $k$ is a natural number compared as a real. Of the standing assumptions of §4 (p. 70), strict primal feasibility is the start $x^{(0)}\in\mathbf X$; linear independence of $F_1,\dots,F_m$ is not a separate hypothesis because it follows from $\mathbf X$ being nonempty and bounded (if $\sum_iv_iF_i=0$ then $x^{(0)}+tv\in\mathbf X$ for every $t$); strict dual feasibility concerns the cost vector $c$, which does not occur in this theorem. Indices are zero-based.
--
--   Differences from the source:
--   - encoding: "x⁽ᵏ⁾ the value of x in the previous algorithm after the kth iteration" → an arbitrary run (an infinite sequence; the algorithm has no stopping rule) and an arbitrary k; reason: same statement.
--   - encoding: exact line search "p̂ = argmin ϕ(x + pδxᴺ)" → minimality over the real p with F(x + pδxᴺ) > 0; reason: ϕ = +∞ elsewhere on the page and Lean's real-valued barrier is junk there.
--   - encoding: standing assumptions of §4 and the boundedness assumption of §§4.2–4.3 → hypotheses (symmetric data, X bounded, strictly feasible start); linear independence omitted as implied, strict dual feasibility omitted because c does not occur; reason: no instance of the source is excluded or added.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 73 (PDF p. 25), Theorem 4.1; algorithm p. 72 (PDF p. 24); (42) p. 70; (46) and boundedness p. 71 (PDF p. 23); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsAnalyticCenter
import Definitions.Def_VBSDP_Duality_Supplement_IsNewtonRun

namespace VBSDP.Duality.Supplement

theorem theorem_4_1 {m n : ℕ}
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hbdd : Bornology.IsBounded {x : Fin m → ℝ | (VBSDP.Duality.lmi F₀ F x).PosDef})
    (xk : ℕ → Fin m → ℝ) (hrun : IsNewtonRun F₀ F xk)
    (xs : Fin m → ℝ) (hxs : IsAnalyticCenter F₀ F xs)
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 0.5) (k : ℕ)
    (hk : 11 * (barrier F₀ F (xk 0) - barrier F₀ F xs) + Real.logb 2 (Real.logb 2 (1 / ε)) ≤ k) :
    barrier F₀ F (xk k) - barrier F₀ F xs ≤ ε := by sorry

end VBSDP.Duality.Supplement
