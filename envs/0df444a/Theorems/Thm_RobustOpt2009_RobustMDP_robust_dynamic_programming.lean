-- Prove2me | Theorems.Thm_RobustOpt2009_RobustMDP_robust_dynamic_programming
-- name    : RobustOpt2009.RobustMDP.robust_dynamic_programming
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:37.986641+00:00
-- url     : https://prove2.me/theorems/3c9db09f-079a-4756-bc2f-e01d54bb76ea
-- title:
--   Theorem 13.3.1 — Robust Dynamic Programming
-- statement:
--   Let $X$ and $A$ be finite nonempty sets, $N$ a finite horizon, $c_t(i,a)$ and $c_N(i)$ real costs, and $q_0$ an arbitrary initial probability distribution. At every time, state and action, let $P_{ti}^a$ be a nonempty closed subset of the probability simplex. Nature may choose every row independently from its specified set. Controller policies are deterministic Markov policies. Let $C_{t,q}(u,p)$ denote expected remaining cost, defined by forward state distributions.
--
--   Initialize $v_N=c_N$ and compute
--   $$v_t(i)=\min_{a\in A}\left[c_t(i,a)+\max_{p\in P_{ti}^a}\sum_jp(j)v_{t+1}(j)\right].$$
--   For every $t\le N$ and $i\in X$, this equals the attained minimum over control policies of the worst expected remaining cost starting at $(t,i)$. The robust problem has attained value
--   $$\min_u\max_p C_{0,q_0}(u,p)=q_0^Tv_0.$$
--   Policies satisfying the following selection rules exist:
--   $$u_t^*(i)\in\arg\min_a\left[c_t(i,a)+\max_{p\in P_{ti}^a}p^Tv_{t+1}\right],\qquad p_{ti}^{a,*}\in\arg\max_{p\in P_{ti}^a}p^Tv_{t+1}.$$
--   Every such controller is optimal at all times and states. Its attained worst expected cost from $q_0$ is $q_0^Tv_0$, and every pair selected by these rules attains that cost.
--
--   Finally, for every fixed controller $u$, the recursion
--   $$v_N^u=c_N,\qquad v_t^u(i)=c_t(i,u_t(i))+\max_{p\in P_{ti}^{u_t(i)}}p^Tv_{t+1}^u$$
--   gives its attained worst remaining cost at every time and state and its attained worst total cost $q_0^Tv_0^u$.
--
--   This is the full finite-horizon robust Bellman theorem, including policy extraction and fixed-policy evaluation.
--
--   **Formalization Note** Concrete recursions are compared with independently defined forward expected costs. Minima and maxima are expressed with `IsLeast` and `IsGreatest`; explicit policy-existence clauses retain attainment. The internal real suprema have nonempty bounded domains because all nature rows are probability vectors and the horizon is finite; closedness supplies row maximizers. No convexity, stationary-row restriction, nonnegative-cost restriction, or point-mass restriction on $q_0$ is added. Suffix policies are encoded by full policies whose earlier coordinates are ignored. The empty horizon gives terminal cost.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 13.3.1, printed p. 350 (PDF p. 376); standing assumptions printed pp. 343–344, 348–349.

import Mathlib

namespace RobustOpt2009.RobustMDP
namespace Robust

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

/-- Time-dependent rectangular uncertainty; no convexity or sign condition on costs. -/
structure Model (n m N : ℕ) extends Data n m N where
  rows : Fin N → Fin n → Fin m → Set (Fin n → ℝ)
  rows_nonempty : ∀ t i a, (rows t i a).Nonempty
  rows_closed : ∀ t i a, IsClosed (rows t i a)
  rows_simplex : ∀ t i a, rows t i a ⊆ stdSimplex ℝ (Fin n)

abbrev Nature {n m N : ℕ} (M : Model n m N) :=
  {P : Transition n m N // ∀ t i a, P t i a ∈ M.rows t i a}

/-- The expression inside the minimum in (13.3.1). -/
noncomputable def actionValue {n m N : ℕ} (M : Model n m N)
    (t : Fin N) (i : Fin n) (a : Fin m) (v : Fin n → ℝ) : ℝ :=
  M.cost t i a + sSup ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' M.rows t i a)

/-- Backward recursion (13.3.1). The theorem identifies it with the independent game value. -/
noncomputable def robustValue {n m N : ℕ} (M : Model n m N) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then fun i => ⨅ a : Fin m, actionValue M ⟨t, h⟩ i a (robustValue M (t + 1))
  else M.terminal
termination_by N - t

/-- Fixed-policy backward recursion (13.3.4). -/
noncomputable def policyValue {n m N : ℕ} (M : Model n m N)
    (u : Control n m N) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then fun i => actionValue M ⟨t, h⟩ i (u ⟨t, h⟩ i) (policyValue M u (t + 1))
  else M.terminal
termination_by N - t

/-- Worst cost over the full product of admissible nature rows. -/
noncomputable def worstCost {n m N : ℕ} (M : Model n m N) (u : Control n m N)
    (s : ℕ) (q : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun P : Nature M => costFrom M.toData u P.val s q)

/-- Rule (13.3.2). -/
def Greedy {n m N : ℕ} (M : Model n m N) (u : Control n m N) : Prop :=
  ∀ (t : Fin N) (i : Fin n) (a : Fin m),
    actionValue M t i (u t i) (robustValue M (t.val + 1)) ≤
      actionValue M t i a (robustValue M (t.val + 1))

/-- Rule (13.3.3): every selected row actually attains the row maximum. -/
def WorstRows {n m N : ℕ} (M : Model n m N) (P : Nature M) : Prop :=
  ∀ (t : Fin N) (i : Fin n) (a : Fin m),
    IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j * robustValue M (t.val + 1) j) '' M.rows t i a)
      (∑ j, P.val t i a j * robustValue M (t.val + 1) j)

end Robust

theorem robust_dynamic_programming {n m N : ℕ} [Nonempty (Fin n)] [Nonempty (Fin m)]
    (M : Robust.Model n m N) (q : Fin n → ℝ) (hq : q ∈ stdSimplex ℝ (Fin n)) :
    (∀ (t : ℕ), t ≤ N → ∀ i : Fin n,
      IsLeast (Set.range fun u : Robust.Control n m N =>
        Robust.worstCost M u t (Robust.pointMass i)) (Robust.robustValue M t i)) ∧
    IsLeast (Set.range fun u : Robust.Control n m N => Robust.worstCost M u 0 q)
      (∑ i, q i * Robust.robustValue M 0 i) ∧
    (∃ u : Robust.Control n m N, Robust.Greedy M u) ∧
    (∃ P : Robust.Nature M, Robust.WorstRows M P) ∧
    (∀ u : Robust.Control n m N, Robust.Greedy M u →
      (∀ (t : ℕ), t ≤ N → ∀ i : Fin n,
        Robust.worstCost M u t (Robust.pointMass i) = Robust.robustValue M t i) ∧
      IsGreatest (Set.range fun P : Robust.Nature M => Robust.costFrom M.toData u P.val 0 q)
        (∑ i, q i * Robust.robustValue M 0 i)) ∧
    (∀ (u : Robust.Control n m N) (P : Robust.Nature M),
      Robust.Greedy M u → Robust.WorstRows M P →
      Robust.costFrom M.toData u P.val 0 q = ∑ i, q i * Robust.robustValue M 0 i) ∧
    (∀ u : Robust.Control n m N,
      (∀ (t : ℕ), t ≤ N → ∀ i : Fin n,
        IsGreatest (Set.range fun P : Robust.Nature M =>
          Robust.costFrom M.toData u P.val t (Robust.pointMass i)) (Robust.policyValue M u t i)) ∧
      IsGreatest (Set.range fun P : Robust.Nature M => Robust.costFrom M.toData u P.val 0 q)
        (∑ i, q i * Robust.policyValue M u 0 i)) := by sorry

end RobustOpt2009.RobustMDP
