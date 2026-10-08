-- Prove2me | Theorems.Thm_SennottDP_SEN_prop_7_7_2_h_acoi
-- name    : SennottDP.SEN.prop_7_7_2_h_acoi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:29:30.590852+00:00
-- url     : https://prove2.me/theorems/6d037903-a24a-4df4-8770-fff9280b98a3
-- title:
--   Proposition 7.7.2 — the conclusions of Theorem 7.2.3 hold under the weaker (H) assumptions
-- statement:
--   Let $\Delta$ be an MDC for which the (H) assumptions hold for the distinguished state $z$, with function $M$ in (H2) and function $L$ in (H3). Then the conclusions of Theorem 7.2.3 are valid, with $L$ the function from (H3):
--
--   1. there is a finite constant $J = \lim_{\alpha\to 1^-}(1-\alpha)V_\alpha(i)$ for every $i$;
--   2. a limit function exists; every limit function $h$ satisfies $-L(i) \le h(i) \le M(i)$ and
--   $$J + h(i) \ge \min_{a \in A_i} \Big\{ C(i,a) + \sum_j P_{ij}(a) h(j) \Big\}, \qquad i \in S; \qquad (7.9)$$
--   every stationary policy $e$ realizing this minimum is average cost optimal with $J_e \equiv J$, and $\lim_n \frac1n E_e[h(X_n) \mid X_0 = i] = 0$;
--   3. every limit point $f$ of stationary policies realizing the discount optimality equation is average cost optimal, has an associated limit function, and every associated $h$ satisfies (7.11) and (7.12);
--   4. for every average cost optimal policy $\psi$ and every $i$, $J_\psi(i) = \lim_n v_{\psi,n}(i)/n$.
--
--   **Formalization Note** The statement is Theorem 7.2.3's, with the (H) assumptions in place of (SEN) and $-L(i) \le h(i)$ in place of $-L \le h$; conventions are as there.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 158, Proposition 7.7.2 (conclusions of Theorem 7.2.3, pp. 134–135)

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.SEN

/-- Sennott (1999), Proposition 7.7.2, p. 158: let `Δ` be an SennottDP.Discounted.MDC for which the (H) assumptions
hold for the distinguished state `z`, with function `Mf` in (H2) and function `Lf` in (H3). Then
the conclusions of Theorem 7.2.3 are valid, where `L` is the function `Lf` from (H3):

(i) there is a finite constant `J = lim_{α→1⁻} (1 − α) V_α(i)` for all `i`;
(ii) a limit function exists; every limit function `h` satisfies `−Lf ≤ h ≤ Mf` and the average
cost optimality inequality (7.9); every stationary policy `e` realizing the minimum in (7.9) is
average cost optimal with average cost `J`, and (7.10) holds;
(iii) every limit point `f` of discount optimal stationary policies is average cost optimal, has
an associated limit function, and every associated `h` satisfies (7.11) and (7.12);
(iv) the average cost under any average cost optimal policy is obtained as a limit. -/
theorem prop_7_7_2_h_acoi {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf Lf : S → ℝ) (hH : HAssumptions M z Mf Lf) :
    ∃ J : ℝ≥0,
      -- (i)
      (∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1)
        (𝓝 (J : ℝ≥0∞))) ∧
      -- (ii)
      (∃ h : S → ℝ, IsLimitFunction M z h) ∧
      (∀ h : S → ℝ, IsLimitFunction M z h →
        (∀ i, -Lf i ≤ h i ∧ h i ≤ Mf i) ∧
        (∀ i, acoiMin M h i ≤ (((J : ℝ) + h i : ℝ) : EReal)) ∧
        ∀ e : StationaryPolicy M, RealizesACOI M h e →
          IsAverageOptimal M e.toPolicy ∧ (∀ i, avgCost M e.toPolicy i = (J : ℝ≥0∞)) ∧
          ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h)
            atTop (𝓝 0)) ∧
      -- (iii)
      (∀ fam : ℝ → StationaryPolicy M, (∀ α ∈ Set.Ioo (0 : ℝ) 1, RealizesDOE M α (fam α)) →
        ∀ f : StationaryPolicy M, IsLimitPoint M fam f →
          IsAverageOptimal M f.toPolicy ∧
          (∃ h : S → ℝ, IsAssociated M z fam f h) ∧
          ∀ h : S → ℝ, IsAssociated M z fam f h →
            (∀ i, ((M.C i (f.1 i) : ℝ) : EReal) + wsum (M.P i (f.1 i)) h ≤
              (((J : ℝ) + h i : ℝ) : EReal)) ∧
            ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M f.toPolicy i n h)
              atTop (𝓝 0)) ∧
      -- (iv)
      (∀ ψ : SennottDP.Discounted.Policy M, IsAverageOptimal M ψ → ∀ i,
        Tendsto (fun n : ℕ => horizonCost M ψ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost M ψ i))) := by sorry

end SennottDP.SEN
