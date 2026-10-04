-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_thm_6_3_1_acoe
-- name    : SennottDP.AvgFinite.thm_6_3_1_acoe
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T08:54:56.41024+00:00
-- url     : https://prove2.me/theorems/fefe0d81-f4e8-4b61-a5de-6bb9f532afcd
-- title:
--   Theorem 6.3.1 — the multichain average cost optimality equation for the Blackwell optimal policy
-- statement:
--   Let $\Delta$ be an MDC with a finite state space $S$. Let $f$ and $\alpha_0 \in (0,1)$ be as in Proposition 6.2.3, i.e. $f$ is a stationary policy that is $\alpha$ discount optimal for every $\alpha \in (\alpha_0,1)$. Let $R_1,\ldots,R_K$ be the positive recurrent classes of the chain induced by $f$, choose distinguished states $z_k \in R_k$, and let $p_k$, $J_k$, $m_{i|k}(f)$, $c_{i|k}(f)$, $W_\alpha(i) = \sum_k p_k(i) V_\alpha(z_k)$ and $w_\alpha(i) = V_\alpha(i) - W_\alpha(i)$ be as defined in Section 6.3. Then for all $i \in S$:
--
--   1. $J(i) = \lim_{\alpha \to 1^-} (1-\alpha) W_\alpha(i)$;
--   2. $\lim_{\alpha \to 1^-} w_\alpha(i) =: w(i) = \sum_k p_k(i)\,[c_{i|k}(f) - J_k\, m_{i|k}(f)]$;
--   3. $\lim_{n \to \infty} E_f[w(X_n) \mid X_0 = i]/n = 0$;
--   4. the average cost optimality equation holds:
--   $$J(i) + w(i) = C(i,f) + \sum_j P_{ij}(f)\, w(j) \ \ge\ \min_{a \in A_i} \Big\{ C(i,a) + \sum_j P_{ij}(a)\, w(j) \Big\}; \tag{6.6}$$
--   5. if $e$ is a stationary policy realizing the minimum in (6.6) and the Markov chain induced by $e$ is positive recurrent at $i$, then (6.6) is an equality at $i$ and $J_e(i) = J(i)$.
--
--   No unichain assumption is made; Example 6.3.2 shows that the inequality in (6.6) can be strict.
--
--   **Formalization Note** The objects of §6.3 are constructed from $f$ in `Def_SennottDP_AvgFinite_ACOE`; the choice of distinguished states is a hypothesis `IsDistinguishedSet` on a finite set `Z` (one state per positive recurrent class), over which the theorem is universally quantified. $W_\alpha$ is in `ℝ≥0∞`, and part 1 is a limit in `ℝ≥0∞`; $w_\alpha$, $w$ and the equation (6.6) are real valued, using `toReal` of quantities that are finite for a finite state space. $\alpha \to 1^-$ is the filter `𝓝[<] 1`. "Realizing the minimum" means $e(j)$ attains the minimum in (6.6) at every state $j$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 101–102, Theorem 6.3.1, Eq. (6.6); objects defined on p. 101

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_ACOE

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Theorem 6.3.1 (Sennott, pp. 101–102). Let `S` be finite, let `f` and `α₀ ∈ (0,1)` be as in
Proposition 6.2.3 (`f` is `α` discount optimal for every `α ∈ (α₀,1)`), and let `Z` contain one
distinguished state `z_k` from each positive recurrent class `R_k` of the chain induced by `f`.
With `W_α`, `w_α` as defined on p. 101, for every `i ∈ S`:
(i) `J(i) = lim_{α→1⁻} (1−α)W_α(i)`;
(ii) `lim_{α→1⁻} w_α(i) =: w(i) = ∑_k p_k(i)[c_{i|k}(f) − J_k m_{i|k}(f)]`;
(iii) `lim_{n→∞} E_f[w(X_n) | X_0 = i]/n = 0`;
(iv) the average cost optimality equation
`J(i) + w(i) = C(i,f) + ∑_j P_{ij}(f) w(j) ≥ min_a {C(i,a) + ∑_j P_{ij}(a) w(j)}` (6.6) holds;
(v) if `e` is a stationary policy realizing the minimum in (6.6) and the chain induced by `e` is
positive recurrent at `i`, then (6.6) is an equality at `i` and `J_e(i) = J(i)`. -/
theorem thm_6_3_1_acoe {S : Type*} {Act : Type*} [Fintype S] (M : MDC S Act)
    (f : StationaryPolicy M) (α₀ : ℝ) (hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    let w : S → ℝ := relValue M f Z
    let rhs : S → Act → ℝ := fun j a => (M.C j a : ℝ) + ∑ k, (M.P j a k).toReal * w k
    let minRhs : S → ℝ := fun j => (M.A j).inf' (M.A_nonempty j) (rhs j)
    -- (i)
    Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * Wdisc M f Z α i) (𝓝[<] 1)
        (𝓝 (avgValue M i)) ∧
    -- (ii)
    Tendsto (fun α : ℝ => wdisc M f Z α i) (𝓝[<] 1) (𝓝 (w i)) ∧
    -- (iii)
    Tendsto (fun n : ℕ => (∑ j, (nStep (inducedChain M f) n i j).toReal * w j) / (n : ℝ))
        atTop (𝓝 0) ∧
    -- (iv)
    ((avgValue M i).toReal + w i = rhs i (f.f i) ∧ rhs i (f.f i) ≥ minRhs i) ∧
    -- (v)
    (∀ e : StationaryPolicy M, (∀ j, rhs j (e.f j) = minRhs j) →
      PositiveRecurrent (inducedChain M e) i →
      (avgValue M i).toReal + w i = minRhs i ∧ avgCost e.toPolicy i = avgValue M i) := by sorry

end SennottDP.AvgFinite
