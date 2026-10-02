-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_liminf_valueN_ge
-- name    : SennottDP.FiniteHorizon.liminf_valueN_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:33:04.606471+00:00
-- url     : https://prove2.me/theorems/92029d6c-342b-40dc-8551-1fef1069db27
-- title:
--   Lemma 3.2.2 — $v^N_{\alpha,0} \to v_{\alpha,0}$ and $\liminf_N v^N_{\alpha,n} \ge v_{\alpha,n}$
-- statement:
--   Let $(\Delta_N)$ be an approximating sequence for the MDC $\Delta$ (countable state space, terminal cost $F$ shared by all $\Delta_N$) and $0 < \alpha \le 1$. Then for every $i \in S$
--   $$
--   \lim_{N\to\infty} v^N_{\alpha,0}(i) = v_{\alpha,0}(i), \qquad \liminf_{N\to\infty} v^N_{\alpha,n}(i) \ \ge\ v_{\alpha,n}(i) \quad (n \ge 1).
--   $$
--
--   This is what holds for every approximating sequence without further assumptions; it supplies half of the convergence in Theorem 3.2.3.
--
--   **Formalization Note** $v^N_{\alpha,n}(i)$ is defined for $N \ge N_0$ with $i \in S_N$; the remaining finitely many terms are set to $0$ and do not affect the limit or the limit inferior.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 42, Lemma 3.2.2

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Lemma 3.2.2 (Sennott, p. 42). Let `(Δ_N)` be an approximating sequence for `Δ`, with the
terminal cost `F` of `Δ`, and `0 < α ≤ 1`. Then `lim_{N → ∞} v^N_{α,0}(i) = v_{α,0}(i)` for every
`i ∈ S`, and for `n ≥ 1`, `lim inf_{N → ∞} v^N_{α,n}(i) ≥ v_{α,n}(i)` for every `i ∈ S`. -/
theorem liminf_valueN_ge {S Act : Type} [Countable S] (M : MDC S Act) (F : S → ℝ≥0)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1) (AS : M.ApproxSeq) :
    (∀ i, Tendsto (fun N => AS.valueN F α 0 N i) atTop (𝓝 (M.value F α 0 i))) ∧
    (∀ n, 1 ≤ n → ∀ i, M.value F α n i ≤ liminf (fun N => AS.valueN F α n N i) atTop) := by sorry

end SennottDP.FiniteHorizon
