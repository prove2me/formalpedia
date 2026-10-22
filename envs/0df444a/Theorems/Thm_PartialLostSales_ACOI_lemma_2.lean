-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_lemma_2
-- name    : PartialLostSales.ACOI.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:53.925718+00:00
-- url     : https://prove2.me/theorems/c17f85d5-40c2-422e-bbfd-c6e818a416a5
-- title:
--   Lemma 2, p. 12 — under (W*) and (B): w* = lim (1−α)v_α(z), and a stationary average-cost optimal policy satisfies the ACOI
-- statement:
--   Let $(\mathbb X,\mathbb A,c,q)$ be a Markov decision process whose state and action spaces are Borel spaces (Borel subsets of Polish spaces). Its one-step cost $c$ is bounded below and its transition probability is $q$. Write $v_\alpha(x)$ for the optimal $\alpha$-discounted cost and $w(x)$ for the optimal average cost per period, both infima over all history-dependent randomized policies. Let $m_\alpha=\inf_x v_\alpha(x)$ and $u_\alpha=v_\alpha-m_\alpha$.
--
--   Suppose Assumption (W*) holds: $c$ is $\mathbb K$-inf-compact and $q$ is weakly continuous. Suppose also that Assumption (B) holds:
--
--   1. $w^*:=\inf_x w(x)<\infty$;
--   2. there is $\alpha_*\in(0,1)$ with $\sup_{\alpha\in[\alpha_*,1)}u_\alpha(x)<\infty$ for every state $x$.
--
--   Then $w^*=\lim_{\alpha\uparrow1}(1-\alpha)v_\alpha(x)$ for every $x$. Moreover, there are a sequence $\alpha_n\uparrow1$ and a stationary policy $\varphi$ that is average-cost optimal among all policies and satisfies the **average cost optimality inequality** (ACOI)
--   $$w^*+u(x)\ \ge\ c(x,\varphi(x))+\int u(y)\,q(dy\mid x,\varphi(x))\qquad\text{for all }x,$$
--   where
--   $$u(x):=\liminf_{n\to\infty,\ y\to x}u_{\alpha_n}(y).$$
--   Here $w^*$ and $u$ are finite.
--
--   This is the general sufficient condition of Feinberg (2016), which the paper cites and does not prove. Applied to the COMDP, whose state space is the set of beliefs with finite second moment, it gives Theorem 1 once (W*), B(i) (Lemma 3) and B(ii) (Theorem 2) are verified.
--
--   **Formalization Note.** The MDP is the published `FeinbergLiang.ACOE.MDP`. The cost is `lower + cost` with `cost` valued in $[0,\infty]$, and every value is the nonnegative part of the paper's value. The constant `lower` cancels from the limit and from both sides of the ACOI, so the statements for the nonnegative parts are exactly the paper's. "$\alpha\to1$" is the limit from the left. "Stationary" means a measurable selector $\varphi:\mathbb X\to\mathbb A$.
--
--   The finiteness of $w^*$ and of $u$ is stated explicitly, so that the ACOI is an inequality between real numbers. This is no strengthening, because both follow from (B). Borel spaces are encoded as metrizable, second-countable spaces whose σ-algebra is Borel and standard Borel.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 12, Lemma 2 (cited from Feinberg 2016)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- Lemma 2, p. 12 (Feinberg 2016), for an MDP on Borel spaces: under Assumptions (W*) and (B),
`w* = lim_{α ↑ 1} (1 − α) v_α(x)` for every `x`, and there is a stationary average-cost optimal
policy satisfying the ACOI `w* + u(x) ≥ c(x, φ(x)) + ∫ u(y) q(dy | x, φ(x))`, where
`u(x) = liminf_{n → ∞, y → x} u_{α_n}(y)` for a sequence `α_n ↑ 1`. -/
theorem lemma_2 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : MDP X A) (hW : AssumptionWStar M) (hB : AssumptionBpaper M) :
    (∀ x, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * vOpt M α x) (𝓝[<] 1)
      (𝓝 (⨅ y, wOpt M y))) ∧
    ∃ αs : ℕ → ℝ, IsDiscountSeq αs ∧
    ∃ φ : X → A, ∃ hφ : Measurable φ,
      IsAvgOptimal M (Policy.ofStationary φ hφ) ∧
      (⨅ y, wOpt M y) ≠ ⊤ ∧ (∀ x, uTilde M αs x ≠ ⊤) ∧
      ∀ x, M.cost x (φ x) + ∫⁻ y, uTilde M αs y ∂(M.q (x, φ x)) ≤
        (⨅ y, wOpt M y) + uTilde M αs x := by sorry

end PartialLostSales.ACOI
