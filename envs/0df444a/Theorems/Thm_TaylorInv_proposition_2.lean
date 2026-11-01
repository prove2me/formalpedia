-- Prove2me | Theorems.Thm_TaylorInv_proposition_2
-- name    : TaylorInv.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:24.954516+00:00
-- url     : https://prove2.me/theorems/4cabfff3-4c90-4c36-97e0-8555e3bd7092
-- title:
--   Proposition 2 — closed form of the Taylor allocation
-- statement:
--   Fix a feature outcome and suppose the retailers are indexed so that $m_1\le m_2\le\cdots\le m_J$. Define $\tilde a_k=\sum_{i=k}^J(\tilde s_i^e-m_kr_i)$. For every $z_0>0$ the Taylor problem (14) has a unique minimizer $\tilde z(z_0,x)$ over $\{z\ge0,\ \sum_jz_j\le z_0\}$, and:
--
--   1. if $z_0>\tilde a_1$,
--   $$
--   \tilde z_j(z_0,x)=\begin{cases}\tilde s_j^e-\dfrac{r_j}{\sum_{i=1}^Jr_i}\Big(\sum_{i=1}^J\tilde s_i^e-z_0\Big),& z_0<\sum_{i}\tilde s_i^e,\\[4pt] \tilde s_j^e,& z_0\ge\sum_i\tilde s_i^e;\end{cases}
--   $$
--   2. if $\tilde a_{k+1}<z_0\le\tilde a_k$ for some $k\in\{1,\dots,J-1\}$,
--   $$
--   \tilde z_j(z_0,x)=\begin{cases}0,& j\le k,\\ \tilde s_j^e-\dfrac{r_j}{\sum_{i=k+1}^Jr_i}\Big(\sum_{i=k+1}^J\tilde s_i^e-z_0\Big),& j>k.\end{cases}
--   $$
--   The statement holds at every feature outcome where $f_j(s_j^l\mid x_j)>0$ (so that $r_j$ is defined) and $s_j^l\ge0$ (demand is nonnegative) for all $j$, with $0\le h_0$ and $b_j+h'_j>0$. Proposition 2 is stated in §4.2, before Assumptions 1–3 are introduced (§4.3), so they are not assumed.
--
--   This closed form replaces the search for a Lagrange multiplier and is what the proof of Theorem 1 evaluates on the three regions.
--
--   **Formalization Note** With 0-based indices, the paper's $\tilde a_k$ is `aT ⟨k-1, _⟩`, "$j\le k$" is `j.val < k`, and $\sum_{j=k+1}^J$ is the sum over `k ≤ j.val`.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: retailers $j\in[J]^+$ and features $p\in[P]^+$ → `Fin J` and `Fin P` (0-based); reason: Lean convention; same instances
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
--   - encoding: $z_j>0$, $z_0>0$ in (5) and (14) → $z_j\ge0$, $z_0\ge0$; reason: (6) uses $z_j\ge0$; the argmin of (14) has zero coordinates in case (16); the infimum (5) is unchanged
--   - encoding: Proposition 2 in the model of §3–§4.2 (any conditional demand distribution, before Assumptions 1–3) → the mission's linear-demand `Model`, at every outcome with $f_j(s_j^l\mid x_j)>0$ and $s_j^l\ge0$, with $0\le h_0$ and no Assumptions 1–3; reason: (14)–(16) depend on the distribution only through $s_j^l$, $r_j$ and $h_0$, and every $s_j^l\ge0$, $r_j>0$ arises in the linear model; the two conditions are what (14) presupposes ($r_j$ defined, demand nonnegative), and $0\le h_0$ is the cost order of p.8
--   - encoding: the reindexing $m_1\le\dots\le m_J$ without loss of generality → the order is a hypothesis on the outcome; reason: the paper's reindexing depends on $x$; same statement
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, Proposition 2, p.13

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- Proposition 2 (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.13): with the retailers
indexed so that `m₁ ≤ m₂ ≤ ⋯ ≤ m_J` and `ã_k = ∑_{i=k}^J (s̃_i^e − m_k r_i)`, the Taylor problem (14)
has a unique minimizer `z̃(z₀, x)`, given for `z₀ > 0` by (15) when `z₀ > ã₁` and by (16) when
`ã_{k+1} < z₀ ≤ ã_k`, `k ∈ {1, …, J − 1}`.

**Formalization Note** Retailers are `Fin J` (0-based): the paper's retailer `k` is index `k − 1`,
so `ã_k` is `aT ⟨k − 1, _⟩`, "`j ≤ k`" is `j.val < k`, and `∑_{j=k+1}^J` is the sum over
`k ≤ j.val`. The sorted order is a hypothesis on the outcome `ω` (the paper's reindexing).
Proposition 2 precedes Assumptions 1–3 (§4.2), so they are not assumed: the statement holds at every
outcome where `f_j(s_j^l | x_j) > 0` (so that `r_j` of p.12 is defined) and `s_j^l ≥ 0` (demand is
nonnegative), with `0 ≤ h₀` (p.8). `0 < b_j + h′_j` excludes only the undefined critical fractile
`0/0`. -/
theorem proposition_2 {J P : ℕ} {Ω : Type*} (M : Model J P Ω)
    (hh₀ : 0 ≤ M.h₀) (hb : ∀ j, 0 < M.b j + M.h' j) :
    ∀ ω, (∀ j, 0 < M.densAtBase j ω) → (∀ j, 0 ≤ M.baseStock j ω) →
      Monotone (fun j => M.m j ω) → ∀ z₀ : ℝ, 0 < z₀ →
      let aT : Fin J → ℝ := fun k =>
        ∑ i ∈ Finset.univ.filter (fun i => k ≤ i), (M.sEch i ω - M.m k ω * M.r i ω)
      (∃! z : Fin J → ℝ, z ∈ feasible z₀ ∧ ∀ z' ∈ feasible z₀, M.taylorObj z ω ≤ M.taylorObj z' ω) ∧
      (∀ hJ : 0 < J, aT ⟨0, hJ⟩ < z₀ →
        M.taAlloc z₀ ω = fun j =>
          if z₀ < ∑ i, M.sEch i ω then
            M.sEch j ω - M.r j ω / (∑ i, M.r i ω) * (∑ i, M.sEch i ω - z₀)
          else M.sEch j ω) ∧
      (∀ k : ℕ, ∀ hk1 : 1 ≤ k, ∀ hkJ : k < J,
        aT ⟨k, hkJ⟩ < z₀ → z₀ ≤ aT ⟨k - 1, by omega⟩ →
        M.taAlloc z₀ ω = fun j =>
          if j.val < k then 0
          else M.sEch j ω - M.r j ω / (∑ i ∈ Finset.univ.filter (fun i : Fin J => k ≤ i.val), M.r i ω)
            * (∑ i ∈ Finset.univ.filter (fun i : Fin J => k ≤ i.val), M.sEch i ω - z₀)) := by sorry

end TaylorInv
