-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_fh_of_augmentation_bound
-- name    : SennottDP.FiniteHorizon.fh_of_augmentation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:46:17.359167+00:00
-- url     : https://prove2.me/theorems/844f47a9-262e-4b81-aff2-2cfa669dec7b
-- title:
--   Proposition 3.3.4 — under (3.20), $v^N_{\alpha,n} \le v_{\alpha,n}$ on $S_N$ and FH(α, n) holds
-- statement:
--   Let $\Delta$ be an MDC with countable state space and terminal cost $F$, and let $0 < \alpha \le 1$. Assume $v_{\alpha,n}(i) < \infty$ for all $i \in S$ and $n \ge 1$. Let $(\Delta_N)$ be an augmentation type approximating sequence whose augmentation distributions satisfy
--   $$
--   \sum_{j \in S_N} q_j(i,a,r,N)\, v_{\alpha,n}(j) \le v_{\alpha,n}(r), \qquad i \in S_N,\ a \in A_i,\ r \in S - S_N,\ n \ge 0. \tag{3.20}
--   $$
--   Then
--   $$
--   v^N_{\alpha,n}(i) \le v_{\alpha,n}(i) \qquad \text{for } i \in S_N,\ n \ge 1,
--   $$
--   and hence Assumption FH($\alpha$, $n$) holds for all $n \ge 1$.
--
--   Condition (3.20) says that redistributing excess probability never raises the expected value above the value at the state the probability would have gone to; it is typically checked through monotonicity of $v_{\alpha,n}$.
--
--   **Formalization Note** As in Proposition 3.3.2, "all $\alpha$" is read as the given $\alpha$, since (3.20) is a condition at that $\alpha$. Condition (3.20) is required for $N \ge N_0$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 49, Proposition 3.3.4, Eq. (3.20)

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Proposition 3.3.4 (Sennott, p. 49). Let `0 < α ≤ 1` and assume `v_{α,n} < ∞` for `n ≥ 1`.
Let `(Δ_N)` be an ATAS whose augmentation distributions satisfy (3.20):
`∑_{j ∈ S_N} q_j(i, a, r, N) v_{α,n}(j) ≤ v_{α,n}(r)` for `i ∈ S_N`, `a ∈ A_i`, `r ∈ S − S_N`,
`n ≥ 0`. Then `v^N_{α,n}(i) ≤ v_{α,n}(i)` for `i ∈ S_N` and `n ≥ 1`; hence FH(α, n) holds. -/
theorem fh_of_augmentation_bound {S Act : Type} [Countable S] (M : MDC S Act)
    (F : S → ℝ≥0) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hfin : ∀ n, 1 ≤ n → ∀ i, M.value F α n i < ⊤)
    (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (h320 : ∀ n N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ AS.SN N, q N i a r j * M.value F α n j ≤ M.value F α n r) :
    (∀ n, 1 ≤ n → ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, AS.valueN F α n N i ≤ M.value F α n i) ∧
    (∀ n, 1 ≤ n → AS.FH F α n) := by sorry

end SennottDP.FiniteHorizon
