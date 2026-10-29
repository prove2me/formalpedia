-- Prove2me | Theorems.Thm_PochetWolsey_BacklogStartup_joint_lp_solves
-- name    : PochetWolsey.BacklogStartup.joint_lp_solves
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:28.89397+00:00
-- url     : https://prove2.me/theorems/a4dd97ec-df79-4b9b-ad94-ff78de5358dc
-- title:
--   Theorem 10.22 — joint backlogging and start-up LP solves the integer model
-- statement:
--   Let $n\ge1$, let demands $d_t\ge0$, and let $M\ge d_{1n}$ be a sufficiently large production bound. Let $h_t\ge0$ for $t=0,\ldots,n$ and $b_t\ge0$ for $t=1,\ldots,n$ be the transformed Wagner–Whitin stock and backlog costs, and let $q_t,g_t$ be real setup and start-up costs. For the original mixed-integer set $X(y_0,d,M)$ and the extended linear formulation $Q(y_0,d)$ of Section 10.6,
--   $$\min_{p\in X(y_0,d,M)} C(p)=\min_{v\in Q(y_0,d)} C(v),$$
--   and both minima are attained. Equivalently, there are an original feasible plan and an extended feasible plan of the same cost, each no more expensive than any feasible point of its respective problem.
--
--   This is the chapter's joint optimization result: the stated extended linear program solves the model with both backlogging and start-up decisions.
--
--   **Formalization Note** The objective omits the constant introduced by eliminating unit production costs. The initial setup state $y_0\in\{0,1\}$ is given as data and $r_0=0$; switch-offs are $w_0,\ldots,w_{n-1}$, with nonnegative initial stock and terminal stock/backlog. The $\alpha,\beta$ domains and final-period indexing follow `JointModel`. Production in the displayed LP is an unused nonnegative coordinate, so the conclusion does not identify its $x$ with the physical production plan. There is no assumption of integrality of LP vertices or equality of feasible sets, and no real infimum with an empty-set default is used.
--
--   Initial-state convention: the parameter `y0` is the same fixed binary datum in every feasible set in this item (printed p. 138 / PDF 155); it is not optimized.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 331 (PDF 344), Theorem 10.22; defining formulation pp. 330–331 (PDF 343–344)

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_JointModel

/-
Imported declaration context (verbatim Lean code, for standalone audit).

```lean
import Mathlib

namespace PochetWolsey.BacklogStartup

noncomputable section

/-- A period vector has coordinates 1,...,n; its extension is zero elsewhere. -/
def period {n : ℕ} (v : Fin n → ℝ) (t : ℕ) : ℝ :=
  if h : 1 ≤ t ∧ t ≤ n then v ⟨t - 1, by omega⟩ else 0

/-- Setup state at time zero is input data (printed p. 138), not a zero default. -/
def setupState {n : ℕ} (y0 : ℝ) (y : Fin n → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then y0 else period y t

/-- Switch-offs are indexed 0,...,n-1, as required by w_(t-1) for t=1,...,n. -/
def switchOff {n : ℕ} (w : Fin n → ℝ) (t : ℕ) : ℝ :=
  period w (t + 1)

/-- A stock vector has coordinates 0,...,n. -/
def stock {n : ℕ} (v : Fin (n + 1) → ℝ) (t : ℕ) : ℝ :=
  if h : t ≤ n then v ⟨t, by omega⟩ else 0

def demandSum {n : ℕ} (d : Fin n → ℝ) (k l : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc k l, period d t

def Binary {n : ℕ} (v : Fin n → ℝ) : Prop := ∀ t, v t = 0 ∨ v t = 1

def UnitBox {n : ℕ} (v : Fin n → ℝ) : Prop := ∀ t, 0 ≤ v t ∧ v t ≤ 1

end
end PochetWolsey.BacklogStartup
```

```lean
import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_Horizon

namespace PochetWolsey.BacklogStartup

noncomputable section

structure JointPoint (n : ℕ) where
  x : Fin n → ℝ
  s : Fin (n + 1) → ℝ
  r : Fin (n + 1) → ℝ
  y : Fin n → ℝ
  z : Fin n → ℝ
  w : Fin n → ℝ

structure JointLift (n : ℕ) where
  point : JointPoint n
  alpha : Fin n → ℝ
  beta : Fin n → ℝ

structure JointCosts (n : ℕ) where
  h : Fin (n + 1) → ℝ
  b : Fin n → ℝ
  q : Fin n → ℝ
  g : Fin n → ℝ

/-- Both kinds of carrying cost are nonnegative after eliminating production costs. -/
def JointCosts.WagnerWhitin {n : ℕ} (c : JointCosts n) : Prop :=
  (∀ t, 0 ≤ c.h t) ∧ (∀ t, 0 ≤ c.b t)

def jointCost {n : ℕ} (c : JointCosts n) (p : JointPoint n) : ℝ :=
  (∑ t, c.h t * p.s t) +
  ∑ t : Fin n, (c.b t * stock p.r (t.val + 1) + c.q t * p.y t + c.g t * p.z t)

/-- The common domains and switch balance, with given y₀, switch-offs w₀,...,w_(n-1), and r₀ = 0. -/
def JointCore {n : ℕ} (y0 : ℝ) (p : JointPoint n) : Prop :=
  (∀ t, 0 ≤ p.x t) ∧ (∀ t, 0 ≤ p.s t) ∧ (∀ t, 0 ≤ p.r t) ∧
  stock p.r 0 = 0 ∧
  (∀ t ∈ Finset.Icc 1 n,
    period p.z t - switchOff p.w (t - 1) = period p.y t - setupState y0 p.y (t - 1) ∧
    period p.z t ≤ period p.y t)

/-- Original mixed-integer formulation on printed p. 330. -/
def JointFeasible {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) (M : ℝ) : Set (JointPoint n) :=
  {p | JointCore y0 p ∧ Binary p.y ∧ Binary p.z ∧ Binary p.w ∧
    ∀ t ∈ Finset.Icc 1 n,
      stock p.s (t - 1) - stock p.r (t - 1) + period p.x t =
        period d t + stock p.s t - stock p.r t ∧
      period p.x t ≤ M * period p.y t}

/-- The displayed extended LP on pp. 330-331. Alpha and beta retain their
nonnegative fraction domains from Section 10.2.3. The adjacent-period inequality
has range 1 ≤ t < n; switch-offs have indices 0,...,n-1. -/
def JointExtended {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) : Set (JointLift n) :=
  {v | JointCore y0 v.point ∧ UnitBox v.point.y ∧ UnitBox v.point.z ∧
    UnitBox v.point.w ∧ (∀ t, 0 ≤ v.alpha t) ∧ (∀ t, 0 ≤ v.beta t) ∧
    (∀ t ∈ Finset.Icc 1 n, 0 < period d t →
      period v.alpha t + period v.point.y t + period v.beta t = 1) ∧
    (∀ t ∈ Finset.Icc 1 (n - 1),
      period v.beta t ≤ period v.beta (t + 1) + period v.point.z (t + 1)) ∧
    (∀ t ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc t n,
      (∑ u ∈ Finset.Icc t k, period d u *
        (period v.alpha u - ∑ j ∈ Finset.Icc t (u - 1), switchOff v.point.w j)) ≤
          stock v.point.s (t - 1)) ∧
    (∀ k ∈ Finset.Icc 1 n, ∀ t ∈ Finset.Icc k n,
      (∑ u ∈ Finset.Icc k t, period d u *
        (period v.beta u - ∑ j ∈ Finset.Icc (u + 1) t, period v.point.z j)) ≤
          stock v.point.r t)}

/-- Projection of the lift is existential elimination, not a hull definition. -/
def JointProjection {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) : Set (JointPoint n) :=
  {p | ∃ a b : Fin n → ℝ, JointLift.mk p a b ∈ JointExtended y0 d}

end
end PochetWolsey.BacklogStartup
```

-/

namespace PochetWolsey.BacklogStartup

theorem joint_lp_solves {n : ℕ} (y0 : ℝ) (hy0 : y0 = 0 ∨ y0 = 1) (hn : 0 < n) (d : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (M : ℝ) (hM : demandSum d 1 n ≤ M)
    (c : JointCosts n) (hc : c.WagnerWhitin) :
    ∃ p ∈ JointFeasible y0 d M, ∃ v ∈ JointExtended y0 d,
      jointCost c p = jointCost c v.point ∧
      (∀ p' ∈ JointFeasible y0 d M, jointCost c p ≤ jointCost c p') ∧
      (∀ v' ∈ JointExtended y0 d, jointCost c v.point ≤ jointCost c v'.point) := by sorry

end PochetWolsey.BacklogStartup
