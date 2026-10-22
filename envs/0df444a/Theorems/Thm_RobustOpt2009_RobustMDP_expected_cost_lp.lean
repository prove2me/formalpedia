-- Prove2me | Theorems.Thm_RobustOpt2009_RobustMDP_expected_cost_lp
-- name    : RobustOpt2009.RobustMDP.expected_cost_lp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:37.272439+00:00
-- url     : https://prove2.me/theorems/62c5ba30-78cd-4c8a-85bf-362bec91a32e
-- title:
--   Theorem 13.1.2 — LO representation of finite-horizon expected cost
-- statement:
--   Let $X$ and $A$ be finite nonempty sets, $N$ a finite horizon, $c_t(i,a)$ arbitrary real stage costs, and $c_N(i)$ terminal costs. Fix a deterministic Markov policy $u$, transition probability rows $p_{ti}^a$, and an initial probability distribution $q_0$. Let $C_N(u,p)$ be the expected total cost, computed from the forward state distributions. Then
--   $$C_N(u,p)=\max_{v_0,\ldots,v_{N-1}}\left\{q_0^Tv_0:\ v_t(i)\le c_t(i,u_t(i))+\sum_jp_{ti}^{u_t(i)}(j)v_{t+1}(j)\quad(0\le t<N,\ i\in X)\right\},$$
--   where $v_N=c_N$, and the maximum is attained.
--
--   This identifies fixed-policy expected cost with the value of a linear optimization problem.
--
--   **Formalization Note** Attainment and the upper-bound property are stated together with `IsGreatest`. The forward-distribution definition implements (13.1.3)–(13.1.4), independently of the LP. Nonempty finite states and actions are represented by `Fin n` and `Fin m`; $N=0$ is permitted and gives terminal expected cost. No positivity of costs or full support of $q_0$ is assumed.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 13.1.2, printed p. 345 (PDF p. 371).

import Mathlib

namespace RobustOpt2009.RobustMDP
namespace FixedPolicy

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

end FixedPolicy

theorem expected_cost_lp {n m N : ℕ} [Nonempty (Fin n)] [Nonempty (Fin m)]
    (D : FixedPolicy.Data n m N) (u : FixedPolicy.Control n m N)
    (P : FixedPolicy.Transition n m N)
    (hP : ∀ t i a, P t i a ∈ stdSimplex ℝ (Fin n))
    (q : Fin n → ℝ) (hq : q ∈ stdSimplex ℝ (Fin n)) :
    IsGreatest
      {x : ℝ | ∃ v : Fin (N + 1) → Fin n → ℝ,
        v (Fin.last N) = D.terminal ∧
        (∀ (t : Fin N) (i : Fin n), v t.castSucc i ≤
          D.cost t i (u t i) + ∑ j, P t i (u t i) j * v t.succ j) ∧
        x = ∑ i, q i * v 0 i}
      (FixedPolicy.costFrom D u P 0 q) := by sorry

end RobustOpt2009.RobustMDP
