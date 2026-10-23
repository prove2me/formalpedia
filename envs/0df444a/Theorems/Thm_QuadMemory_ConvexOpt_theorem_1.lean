-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_theorem_1
-- name    : QuadMemory.ConvexOpt.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:08.142404+00:00
-- url     : https://prove2.me/theorems/6ff484be-8ab2-4536-b852-88f5ccda1cae
-- title:
--   Theorem 1, p. 2 — at accuracy 1/d⁴, a deterministic first-order method with fewer than d^{2−δ} bits of memory makes Ω̃(d^{1+δ/3}) queries
-- statement:
--   For $\epsilon=1/d^4$ and any $\delta\in[0,1]$, a deterministic first-order algorithm guaranteed to minimize $1$-Lipschitz convex functions over the unit ball with $\epsilon$ accuracy uses at least $d^{2-\delta}$ bits or makes $\tilde\Omega(d^{1+\delta/3})$ queries.
--
--   Precisely: for every $\delta\in[0,1]$ there are $C>0$, $K\in\mathbb N$ and $d_0$ such that for every $d\ge d_0$, every $M$-bit memory-constrained deterministic algorithm with $M<d^{2-\delta}$ that, on every $1$-Lipschitz convex $f:\mathbb R^d\to\mathbb R$ and every subgradient selection, stops within $Q$ queries with an output $\tilde x$ satisfying $f(\tilde x)\le\min_{B_d(0,1)}f+1/d^4$, has
--   $$Q\ge\frac{C\,d^{1+\delta/3}}{(\log d)^K}.$$
--
--   Cutting-plane methods such as center of mass reach accuracy $\epsilon$ with $O(d\log(1/\epsilon))$ queries using about $d^2\log(1/\epsilon)$ bits of memory; the theorem shows that no method with memory $d^{2-\delta}$ keeps a near-linear query count, so these methods are Pareto-optimal up to logarithmic factors.
--
--   **Formalization Note.** $\tilde\Omega$ is encoded as $\exists C,K,d_0$, chosen after $\delta$, so the constants may depend on $\delta$; the logarithm is natural (another base changes only $C$). The range $\delta\in[0,1]$ is the page's. At $\delta=0$ the claim is the classical memory-free $\tilde\Omega(d)$ lower bound for deterministic first-order methods, which the paper cites; the paper's own argument (Procedure 1 and Game 2) does not reach that endpoint, so a proof must treat it separately. At $\delta=1$ the hypotheses ($M<d$ bits and accuracy $1/d^4$) cannot be met for large $d$, since $2^M$ possible outputs must form a $1/d^4$-net of the ball; the endpoint is vacuous on the page as well. Queries lie in the unit ball (see the Model module).
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 2, Theorem 1 (proof pp. 25–26)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model

namespace QuadMemory.ConvexOpt

/-- Theorem 1 (Blanchard–Zhang–Jaillet, arXiv:2302.04963v2, p. 2): for `ε = 1/d⁴` and any
`δ ∈ [0, 1]`, an `M`-bit deterministic first-order algorithm that minimizes every `1`-Lipschitz
convex function over the unit ball to accuracy `ε` with at most `Q` queries has `M ≥ d^{2-δ}` or
`Q = Ω̃(d^{1+δ/3})`, i.e. `Q ≥ C d^{1+δ/3} / (log d)^K` for `d ≥ d₀`, where `C, K, d₀` depend only
on `δ`. -/
theorem theorem_1 :
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∀ (M Q : ℕ) (alg : MemAlg d M),
          (M : ℝ) < (d : ℝ) ^ (2 - δ) →
          SolvesCO alg Q (1 / (d : ℝ) ^ 4) →
          C * (d : ℝ) ^ (1 + δ / 3) / Real.log d ^ K ≤ (Q : ℝ) := by sorry

end QuadMemory.ConvexOpt
