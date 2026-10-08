-- Prove2me | Theorems.Thm_SennottDP_SEN_thm_7_2_3_sen_acoi
-- name    : SennottDP.SEN.thm_7_2_3_sen_acoi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:29:03.73831+00:00
-- url     : https://prove2.me/theorems/f216380d-6d3e-44a9-b44c-3dbc514b2a13
-- title:
--   Theorem 7.2.3 — under (SEN) the ACOI holds and optimal stationary policies exist with constant average cost
-- statement:
--   Let $\Delta$ be an MDC for which the (SEN) assumptions hold for the distinguished state $z$, with function $M$ in (SEN2) and constant $L$ in (SEN3).
--
--   1. There is a finite constant $J = \lim_{\alpha \to 1^-} (1-\alpha) V_\alpha(i)$, the same for every $i \in S$.
--   2. A limit function exists. Every limit function $h$ satisfies $-L \le h \le M$ and the **average cost optimality inequality**
--   $$J + h(i) \ge \min_{a \in A_i} \Big\{ C(i,a) + \sum_j P_{ij}(a) h(j) \Big\}, \qquad i \in S. \qquad (7.9)$$
--   Every stationary policy $e$ realizing the minimum in (7.9) is average cost optimal with constant average cost $J_e(i) = J$, and
--   $$\lim_{n\to\infty} \frac1n E_e[h(X_n) \mid X_0 = i] = 0, \qquad i \in S. \qquad (7.10)$$
--   3. For any family $(f_\alpha)$ of stationary policies realizing the discount optimality equation, every limit point $f$ is average cost optimal; a limit function associated with $f$ exists; and every such $h$ satisfies
--   $$J + h(i) \ge C(i,f(i)) + \sum_j P_{ij}(f(i)) h(j), \qquad \lim_{n\to\infty} \frac1n E_f[h(X_n) \mid X_0 = i] = 0, \qquad i \in S. \qquad (7.11),\ (7.12)$$
--   4. For every average cost optimal policy $\psi$ (not necessarily stationary) and every $i$, the average cost is a limit: $J_\psi(i) = \lim_{n\to\infty} v_{\psi,n}(i)/n$.
--
--   This is the central existence theorem for average cost optimization on countable state spaces: it gives a constant minimum average cost, an average cost optimal stationary policy, and two ways to obtain one (from a limit function, or as a limit of discount optimal policies).
--
--   **Formalization Note** $J$ is a nonnegative real (finite). The limit in part 1 is along $\alpha \to 1^-$ (the filter `𝓝[<] 1`) in `ℝ≥0∞`. Sums against $h$ are extended reals (positive minus negative part), finite here because $h \ge -L$. Expectations $E_e[h(X_n)]$ are extended reals, and $\frac1n E$ is multiplication by the real $1/n$ in `EReal`. Part 4 is stated as convergence of $v_{\psi,n}(i)/n$ to $J_\psi(i)$ in `ℝ≥0∞`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 134–135, Theorem 7.2.3, (7.9)–(7.12)

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.SEN

/-- Sennott (1999), Theorem 7.2.3, pp. 134–135: let `Δ` be an SennottDP.Discounted.MDC for which the (SEN) assumptions
hold for the distinguished state `z`, with function `Mf` in (SEN2) and constant `L` in (SEN3).

(i) There exists a finite constant `J = lim_{α→1⁻} (1 − α) V_α(i)` for `i ∈ S`.

(ii) There exists a limit function. Any such function `h` satisfies `−L ≤ h ≤ Mf` and
`J + h(i) ≥ min_a { C(i,a) + ∑_j P_{ij}(a) h(j) }`, `i ∈ S` (7.9). Let `e` be a stationary policy
realizing the minimum in (7.9). Then `e` is average cost optimal with (constant) average cost `J`
and `lim_{n→∞} (1/n) E_e[h(X_n) | X_0 = i] = 0`, `i ∈ S` (7.10).

(iii) Any limit point `f` (of any family `f_α` of stationary policies realizing the discount
optimality equation) is average cost optimal. There exists a limit function associated with `f`.
Any such function `h` satisfies `J + h(i) ≥ C(i,f) + ∑_j P_{ij}(f) h(j)`, `i ∈ S` (7.11), and
`lim_{n→∞} (1/n) E_f[h(X_n) | X_0 = i] = 0`, `i ∈ S` (7.12).

(iv) The average cost under any optimal policy is obtained as a limit:
`J_ψ(i) = lim_{n→∞} v_{ψ,n}(i)/n` for every average cost optimal policy `ψ` and every `i`. -/
theorem thm_7_2_3_sen_acoi {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENAssumptions M z Mf L) :
    ∃ J : ℝ≥0,
      -- (i)
      (∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1)
        (𝓝 (J : ℝ≥0∞))) ∧
      -- (ii)
      (∃ h : S → ℝ, IsLimitFunction M z h) ∧
      (∀ h : S → ℝ, IsLimitFunction M z h →
        (∀ i, -L ≤ h i ∧ h i ≤ Mf i) ∧
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
