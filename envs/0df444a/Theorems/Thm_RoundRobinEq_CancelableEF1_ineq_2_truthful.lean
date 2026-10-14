-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableEF1_ineq_2_truthful
-- name    : RoundRobinEq.CancelableEF1.ineq_2_truthful
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:13.453543+00:00
-- url     : https://prove2.me/theorems/934c23da-fd9a-4028-8550-52a9e1aed604
-- title:
--   §4.2, p. 21 — inequality (2) for the strict truthful deviation of a cancelable agent
-- statement:
--   Let $\succ = (\succ_1, \dots, \succ_n)$ be any profile of rankings with $m = kn$ goods, and let agent $i$ have a cancelable valuation $v_i$. Let $\succ'_i$ be a strict truthful ranking of agent $i$ (it ranks $g$ above $g'$ whenever $v_i(\{g\}) > v_i(\{g'\})$). In Round-Robin$(\succ'_i, \succ_{-i})$ let $x_r$ be the good agent $i$ receives in round $r$. For another agent $j \neq i$, let $A_j = \{y_1, \dots, y_k\}$ be the bundle of $j$ in Round-Robin$(\succ)$, indexed by allocation time in Round-Robin$(\succ'_i, \succ_{-i})$, let $Y_1 = \{y_3, y_5, \dots\}$ and $Y_2 = \{y_2, y_4, \dots\}$, and let $(y^\ell_1, \dots, y^\ell_{\tau_\ell})$ be any Algorithm 3 order of $Y_\ell$ with input $x_1, x_2, \dots$, where $\tau_\ell = |Y_\ell|$. Then for every $\ell \in \{1, 2\}$ and every $r \in [\tau_\ell]$,
--   $$v_i(x_r \mid \{x_1, \dots, x_{r-1}\}) \ge v_i(y^\ell_r \mid \{x_1, \dots, x_{r-1}\}). \tag{2}$$
--
--   This is the analogue, for the truthful deviation of a cancelable agent, of inequality (2) in the proof of Theorem 4.4, where the deviation is the greedy response of Algorithm 4. It says that, round by round, the good agent $i$ secures by deviating is marginally at least as valuable as the matching good of $Y_\ell$.
--
--   **Formalization Note** No equilibrium hypothesis is assumed (the paper's statement is made for an α-approximate PNE; the claim does not use it, so the statement here is stronger). Indices are 0-based: the conclusion is stated for `r < |Y_ℓ|`, where 0-based `r` is the paper's 1-based index $r+1$, so `x r` is $x_{r+1}$ and the prefix `xPrefix x r` is the paper's $\{x_1, \dots, x_{(r+1)-1}\}$. The statement holds for every strict truthful ranking (any tie-breaking among goods of equal singleton value) and every Algorithm 3 order (any tie-breaking). The standing assumption $m = kn$ (p. 7) is a hypothesis; the paper's reduction to it by dummy goods is not formalized.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 21, proof of Theorem 4.5, first paragraph (inequality (2) of p. 20 for the truthful deviation)

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableEF1_Setting
import Definitions.Def_RoundRobinEq_CancelableEF1_DeviationOrders

namespace RoundRobinEq.CancelableEF1

/-- Inequality (2) for the truthful deviation (Amanatidis et al., arXiv:2301.13652v1, §4.2,
p. 21, proof of Theorem 4.5). Agent `i` (cancelable valuation `v i`) deviates from the profile of
rankings `σ` to a strict truthful ranking `τ`; `x` lists `i`'s goods in Round-Robin(τ, σ_{-i}) by
round, `y` lists `A_j` (from Round-Robin(σ), `j ≠ i`) by allocation time in Round-Robin(τ, σ_{-i}),
and `z₁`, `z₂` are the Algorithm 3 renamings `y¹`, `y²` of `Y_1`, `Y_2` with input `x`. Then
`v_i(x_r | {x_1, …, x_{r−1}}) ≥ v_i(y^ℓ_r | {x_1, …, x_{r−1}})` for `ℓ ∈ {1, 2}`, `r ∈ [τ_ℓ]`
(0-based here). No equilibrium hypothesis is needed. -/
theorem ineq_2_truthful {M : Type*} [DecidableEq M] [Fintype M] {n : ℕ} [NeZero n]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (v : Fin n → Finset M → ℝ) (i j : Fin n) (hji : j ≠ i)
    (hvi : RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ RoundRobinEq.CancelableBluff.IsCancelable (v i))
    (σ : Fin n → List M) (hσ : ∀ ℓ, RoundRobinEq.CancelableBluff.IsRanking (σ ℓ))
    (τ : List M) (hτ : IsStrictTruthfulFor (v i) τ)
    (x y z₁ z₂ : ℕ → M)
    (hx : IsRoundEnum (Function.update σ i τ) i k x)
    (hy : IsTimeEnum (Function.update σ i τ) (roundRobin σ j) k y)
    (hz₁ : IsAlg3Order (v i) x (Y1 y k) z₁)
    (hz₂ : IsAlg3Order (v i) x (Y2 y k) z₂) :
    (∀ r < (Y1 y k).card,
        RoundRobinEq.CancelableBluff.marginal (v i) {z₁ r} (xPrefix x r) ≤ RoundRobinEq.CancelableBluff.marginal (v i) {x r} (xPrefix x r)) ∧
      ∀ r < (Y2 y k).card,
        RoundRobinEq.CancelableBluff.marginal (v i) {z₂ r} (xPrefix x r) ≤ RoundRobinEq.CancelableBluff.marginal (v i) {x r} (xPrefix x r) := by sorry

end RoundRobinEq.CancelableEF1
