-- Prove2me | Theorems.Thm_RobustOpt2009_RobustMDP_nominal_dynamic_programming
-- name    : RobustOpt2009.RobustMDP.nominal_dynamic_programming
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:38.740518+00:00
-- url     : https://prove2.me/theorems/effcccc0-f61a-4b18-9d91-820739a45604
-- title:
--   Theorem 13.1.4 — Dynamic Programming algorithm
-- statement:
--   Consider finite nonempty state and action spaces, a horizon $N$, arbitrary real stage and terminal costs, fixed time-dependent transition probability rows $p_{ti}^a$, and initial distribution $q_0$. Define $v_N=c_N$ and
--   $$v_t(i)=\min_{a\in A}\left[c_t(i,a)+\sum_jp_{ti}^a(j)v_{t+1}(j)\right],\qquad t=N-1,\ldots,0.$$
--   For every time $t\le N$ and state $i$, $v_t(i)$ is the attained minimum expected remaining cost over deterministic Markov policies, starting at $i$ at time $t$. The nominal problem's attained minimum from $q_0$ is $q_0^Tv_0$. Greedy policies exist, and every policy satisfying
--   $$u_t^*(i)\in\arg\min_{a\in A}\left[c_t(i,a)+\sum_jp_{ti}^a(j)v_{t+1}(j)\right]$$
--   attains these optimal values at all times and states, and from $q_0$.
--
--   The theorem identifies the backward values with the independently defined control problem and provides an optimal controller.
--
--   **Formalization Note** The recursion is a concrete terminating function. Minima are asserted with `IsLeast`, including attainment. Full-horizon policies encode suffix policies by restriction; coordinates before $t$ do not affect remaining cost and every suffix policy extends. This is the greedy rule evaluated on the recursive values, as Theorem 13.1.4 states; it does not assert greedy optimality for arbitrary optimal solutions of the separate LP (13.1.6).
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 13.1.4 and Eq. (13.1.7), printed p. 346 (PDF p. 372).

import Mathlib

namespace RobustOpt2009.RobustMDP
namespace Nominal

abbrev Control (n m N : ℕ) := Fin N → Fin n → Fin m
abbrev Transition (n m N : ℕ) := Fin N → Fin n → Fin m → Fin n → ℝ

structure Data (n m N : ℕ) where
  cost : Fin N → Fin n → Fin m → ℝ
  terminal : Fin n → ℝ

/-- Forward state distribution from distribution q at stage s. Stages before s
hold q fixed; after N the distribution is held fixed. Only s ≤ t ≤ N is used. -/
noncomputable def dist {n m N : ℕ} (u : Control n m N) (P : Transition n m N)
    (s : ℕ) (q : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => q
  | t + 1 => if h : t < N then
      if s ≤ t then fun j => ∑ i, dist u P s q t i * P ⟨t, h⟩ i (u ⟨t, h⟩ i) j
      else q
    else dist u P s q t

/-- Expected cost from s through N, defined by forward distributions, not Bellman values. -/
noncomputable def costFrom {n m N : ℕ} (D : Data n m N) (u : Control n m N)
    (P : Transition n m N) (s : ℕ) (q : Fin n → ℝ) : ℝ :=
  (∑ t : Fin N, if s ≤ t.val then
    ∑ i, dist u P s q t.val i * D.cost t i (u t i) else 0) +
  ∑ i, dist u P s q N i * D.terminal i

def pointMass {n : ℕ} (i : Fin n) : Fin n → ℝ := fun j => if j = i then 1 else 0

/-- Nominal recursion (13.1.8), with terminal value c_N. -/
noncomputable def nominalValue {n m N : ℕ} (D : Data n m N)
    (P : Transition n m N) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then fun i =>
    ⨅ a : Fin m, D.cost ⟨t, h⟩ i a + ∑ j, P ⟨t, h⟩ i a j * nominalValue D P (t + 1) j
  else D.terminal
termination_by N - t

/-- The action selection rule (13.1.7), evaluated at the recursive value function. -/
def NominalGreedy {n m N : ℕ} (D : Data n m N) (P : Transition n m N)
    (u : Control n m N) : Prop :=
  ∀ (t : Fin N) (i : Fin n) (a : Fin m),
    D.cost t i (u t i) + ∑ j, P t i (u t i) j * nominalValue D P (t.val + 1) j ≤
    D.cost t i a + ∑ j, P t i a j * nominalValue D P (t.val + 1) j

end Nominal

theorem nominal_dynamic_programming {n m N : ℕ} [Nonempty (Fin n)] [Nonempty (Fin m)]
    (D : Nominal.Data n m N) (P : Nominal.Transition n m N)
    (hP : ∀ t i a, P t i a ∈ stdSimplex ℝ (Fin n))
    (q : Fin n → ℝ) (hq : q ∈ stdSimplex ℝ (Fin n)) :
    (∀ (t : ℕ), t ≤ N → ∀ i : Fin n,
      IsLeast (Set.range fun u : Nominal.Control n m N =>
        Nominal.costFrom D u P t (Nominal.pointMass i)) (Nominal.nominalValue D P t i)) ∧
    IsLeast (Set.range fun u : Nominal.Control n m N => Nominal.costFrom D u P 0 q)
      (∑ i, q i * Nominal.nominalValue D P 0 i) ∧
    (∃ u : Nominal.Control n m N, Nominal.NominalGreedy D P u) ∧
    (∀ u : Nominal.Control n m N, Nominal.NominalGreedy D P u →
      (∀ (t : ℕ), t ≤ N → ∀ i : Fin n,
        Nominal.costFrom D u P t (Nominal.pointMass i) = Nominal.nominalValue D P t i) ∧
      Nominal.costFrom D u P 0 q = ∑ i, q i * Nominal.nominalValue D P 0 i) := by sorry

end RobustOpt2009.RobustMDP
