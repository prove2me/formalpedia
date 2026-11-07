-- Prove2me | Theorems.Thm_QuadPTFLearn_theorem_4_1
-- name    : QuadPTFLearn.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:56.820031+00:00
-- url     : https://prove2.me/theorems/7e7d8462-858c-42a6-b95a-98ef7ec015c8
-- title:
--   Theorem 4.1, p.28 — small randomized error on $V^\perp$ implies $\epsilon$-closeness to an intersection of $(\tau,V)$-regular quadratics
-- statement:
--   There is a universal constant $C>1$ such that the following holds. Let $k\ge1$, $\epsilon,\tau\in(0,1)$ and $V\subseteq\mathbb R^d$ a subspace. Suppose $f:\mathbb R^d\to\{0,1\}$ is an intersection of at most $k$ degree-2 PTFs and
--   $$\mathrm{Rand}_f(v)\le\alpha_k(\epsilon,\tau):=\frac{\tau^2\epsilon^2}{Ck^{12}}$$
--   for every unit vector $v\in V^\perp$. Then there are $k'\le k$ polynomials $q_1,\dots,q_{k'}$ of degree at most two such that $g(x)=1\{q_1(x)\ge0,\dots,q_{k'}(x)\ge0\}$ satisfies
--   $$\Pr_{x\sim N(0,I_d)}[f(x)\ne g(x)]\le\epsilon,$$
--   and each $q_i$ is $(\tau,V)$-regular.
--
--   The theorem reduces the learning problem, after dimension reduction, to the regular case where Gaussian comparison applies.
--
--   Differences from the source:
--   - encoding: an intersection of at most k degree-2 PTFs → 1{p_i ≥ 0 ∀ i} for a family p : Fin k₀ → polynomials of degree ≤ 2 with k₀ ≤ k; reason: the same functions
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 4.1, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_QuadPTFLearn_Regularity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 4.1 (Regular approximation from small randomized error), p.28 (PDF p.30).

There is a universal constant `C > 1` such that the following holds. Let `k ≥ 1`,
`ϵ, τ ∈ (0, 1)` and `V ⊆ ℝᵈ` a subspace. If `f` is an intersection of at most `k` degree-2 PTFs
and `Rand_f(v) ≤ α_k(ϵ, τ) := τ²ϵ²/(C k¹²)` for every unit `v ∈ V⊥`, then there are `k′ ≤ k`
polynomials `q₁, …, q_{k′}` of degree at most two such that `g = 1{q₁ ≥ 0, …, q_{k′} ≥ 0}`
satisfies `Pr_{x∼N(0,I_d)}[f(x) ≠ g(x)] ≤ ϵ`, and each `qᵢ` is `(τ, V)`-regular.

**Formalization Note.** "At most `k`" is a family indexed by `Fin k₀` with `k₀ ≤ k`. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 1 < C ∧
      ∀ (d k : ℕ), 1 ≤ k → ∀ ϵ τ : ℝ, 0 < ϵ → ϵ < 1 → 0 < τ → τ < 1 →
      ∀ V : Submodule ℝ (Pt d), ∀ k₀ : ℕ, k₀ ≤ k → ∀ p : Fin k₀ → Poly d, IsQuadFamily p →
        (∀ v ∈ Vᗮ, ‖v‖ = 1 → Rand (ptfInd p) v ≤ τ ^ 2 * ϵ ^ 2 / (C * (k : ℝ) ^ 12)) →
        ∃ k' : ℕ, k' ≤ k ∧ ∃ q : Fin k' → Poly d, IsQuadFamily q ∧
          gauss d {x | ptfInd p x ≠ ptfInd q x} ≤ ENNReal.ofReal ϵ ∧
          ∀ i, IsRegular τ V (q i) := by sorry

end QuadPTFLearn
