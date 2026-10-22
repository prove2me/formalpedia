-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_theorem_1
-- name    : PartialLostSales.ACOI.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:28.629167+00:00
-- url     : https://prove2.me/theorems/34cb6589-3740-435c-af9c-2863e12505c4
-- title:
--   Theorem 1, p. 9 — under Assumption 1, a stationary average-cost optimal policy satisfying the ACOI exists for the partially observed lost-sales model
-- statement:
--   Consider the lost-sales inventory model in which the inventory level is observed only when it is zero, under its standing assumptions. Orders lie in $[0,K]$ with $K>0$ and are delivered immediately at zero ordering cost; demands are i.i.d. and nonnegative, with a density, a finite positive mean and a positive variance; the unit holding and lost-sales costs $h^+,h^-$ are positive. Pass to its COMDP, whose states are beliefs $z$ about the inventory level with finite second moment (Assumption 1), whose cost is $\bar c$ and whose transition kernel is $q$.
--
--   Then there exist a sequence of discount factors $\alpha_n\uparrow1$ and a stationary policy $\varphi$, mapping beliefs to order quantities, with the following properties:
--
--   1. $\varphi$ is average-cost optimal among all history-dependent randomized policies;
--   2. $w^*:=\inf_z w(z)$ is finite, and so is $u(z):=\liminf_{n\to\infty,\,s\to z}u_{\alpha_n}(s)$ for every belief $z$;
--   3. $\varphi$ satisfies the average cost optimality inequality
--   $$w^*+u(z)\ \ge\ \bar c(z,\varphi(z))+\int u(s)\,q(ds\mid z,\varphi(z))\qquad\text{for every belief }z.$$
--
--   This is the main result of the paper: a stationary average-cost optimal policy exists for this partially observed lost-sales system, which had been open (only the discounted case was known).
--
--   **Formalization Note.** The statement is about the COMDP, any MDP satisfying `IsCOMDP`; such an MDP exists, by the milestone `comdp_exists`. The paper notes on p. 10 that COMDP policies and POMDP policies correspond and have the same values (Feinberg, Kasyanov and Zgurovsky 2016), so the COMDP form is the paper's own reading of "for the POMDP model". "Stationary" means a measurable map from beliefs to $[0,K]$.
--
--   The finiteness of $w^*$ and $u$ is stated explicitly, so that the ACOI is an inequality between real numbers rather than one that holds trivially when $u(z)=\infty$. Both follow from Lemma 3 and Theorem 2, so this is no strengthening. Beliefs carry the weak topology induced by the Euclidean topology on $\mathbb R_+$; it enters through the liminf $s\to z$ defining $u$.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 9, Theorem 1 (with the ACOI of Lemma 2, p. 12)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- Theorem 1, p. 9: under Assumption 1 there is a stationary average-cost optimal policy for the
partially observed lost-sales model (in its COMDP form) satisfying the ACOI
`w* + u(z) ≥ c̄(z, φ(z)) + ∫ u(s) q(ds | z, φ(z))`, with `w* = inf_z w(z)` finite and
`u(z) = liminf_{n → ∞, s → z} u_{α_n}(s)` finite for a sequence `α_n ↑ 1`. -/
theorem theorem_1 (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P))
    (hM : IsCOMDP P M) :
    ∃ αs : ℕ → ℝ, IsDiscountSeq αs ∧
    ∃ φ : Bel P → Act P, ∃ hφ : Measurable φ,
      IsAvgOptimal M (Policy.ofStationary φ hφ) ∧
      (⨅ z, wOpt M z) ≠ ⊤ ∧ (∀ z, uTilde M αs z ≠ ⊤) ∧
      ∀ z, M.cost z (φ z) + ∫⁻ s, uTilde M αs s ∂(M.q (z, φ z)) ≤
        (⨅ z, wOpt M z) + uTilde M αs z := by sorry

end PartialLostSales.ACOI
