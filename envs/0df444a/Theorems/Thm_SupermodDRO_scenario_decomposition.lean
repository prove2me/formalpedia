-- Prove2me | Theorems.Thm_SupermodDRO_scenario_decomposition
-- name    : SupermodDRO.scenario_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:04.181238+00:00
-- url     : https://prove2.me/theorems/6f80ad06-489b-4cd1-bf7e-80afa2ab07f2
-- title:
--   §2.3, p.11 — the worst case over $\mathcal F$ decomposes over the scenarios
-- statement:
--   Assume $\mathcal Q\subseteq\{q\ge0:\mathbf 1^\top q=1\}$, $\underline z^k\le\mu^k\le\overline z^k$ and $\delta^k\ge0$ for every $k$, and let $x$ be a first-stage decision with $g(x,\cdot)>-\infty$. Then
--   $$
--   \sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]
--   =\max_{q\in\mathcal Q}\ \sup_{\mathbb P^k\in\mathcal F^k,\,k\in[K]}\ \sum_{k\in[K]}q_k\,\mathbb E_{\mathbb P^k}[g(x,\tilde z)]
--   =\max_{q\in\mathcal Q}\ \sum_{k\in[K]}q_k\sup_{\mathbb P^k\in\mathcal F^k}\mathbb E_{\mathbb P^k}[g(x,\tilde z)],
--   $$
--   and when $\mathcal Q\neq\emptyset$ both maxima are attained by one $q\in\mathcal Q$.
--
--   It separates the choice of the scenario probabilities $q$ from the worst case within each scenario.
--
--   **Formalization Note** $\mathcal F$ consists of joint laws of $(\tilde k,\tilde z)$, so the first equality is a disintegration over the finite variable $\tilde k$, not a definition. Products and sums are in $[-\infty,+\infty]$ with $0\cdot\infty=0$.
--
--   Differences from the source:
--   - generalization: standing assumption that Problem (2) has a finite optimal value → only its consequence g(x, ·) > −∞ is assumed; reason: the standing assumption implies g > −∞ everywhere, so the paper's setting is an instance
--   - generalization: the standing assumptions of §2 (finite value of (2), every scenario possible, the WLOG assumptions of p.7) → only 𝒬 ⊆ simplex and z̲ᵏ ≤ µᵏ ≤ z̄ᵏ, δᵏ ≥ 0; reason: the identity needs only these; the paper's setting is an instance
--   - reading: z̲ᵏ ≤ µᵏ ≤ z̄ᵏ and δᵏ ≥ 0 are never stated → assumed (hypothesis hR); reason: used throughout the paper: the support contains the mean, (5) is a probability vector, and p.7 treats µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ} as the boundary case
--   - encoding: 𝓕 of (3) with constraints conditional on k̃ = k → joint laws of (k̃, z̃) with the conditional constraints multiplied by q_k; reason: identical for q_k > 0; for q_k = 0 the paper's conditioning is undefined and the constraints are void
--   - encoding: max over q ∈ 𝒬 → supremum over 𝒬, and when 𝒬 ≠ ∅ attainment of both outer suprema by one q; reason: this is what max means; for 𝒬 = ∅ both sides are −∞
--   - encoding: expectation of the [−∞, ∞]-valued g → extended expectation ∫g⁺ − ∫g⁻ in EReal, +∞ when ∫g⁺ = ∞; reason: the standard convention; it agrees with the paper whenever the expectation is defined
--   - encoding: [K], [n], [2n+1] indexed from 1 → Fin K, Fin n, Fin (2n+1) indexed from 0; reason: Lean convention; same instances
--   - encoding: g(x, z) = min b⊤y, with g(x, z) = ∞ if (1) is infeasible → the infimum in EReal: ⊤ on an empty feasible set, ⊥ on an unbounded program; reason: same value whenever (1) is infeasible or has an optimal value; the paper never writes the unbounded case
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.3, display before Theorem 1, p.11

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SupermodDRO_QSet
import Definitions.Def_SupermodDRO_scenarioSet
import Definitions.Def_SupermodDRO_scenarioWorstCase
import Definitions.Def_SupermodDRO_worstCaseCost

open MeasureTheory

namespace SupermodDRO

/-- **Decomposition of the worst case over the scenarios.** Long, Qi & Zhang, *Supermodularity in
Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022), §2.3, p.11: "Based on
the definition of 𝓕 and 𝓕ᵏ in Equations (3) and (4), we have
sup_{ℙ∈𝓕} E_ℙ[g(x, z̃)] = max_{q∈𝒬} sup_{ℙᵏ∈𝓕ᵏ, k∈[K]} Σ_{k∈[K]} q_k E_{ℙᵏ}[g(x, z̃)]
= max_{q∈𝒬} Σ_{k∈[K]} q_k sup_{ℙᵏ∈𝓕ᵏ} E_{ℙᵏ}[g(x, z̃)]."

Assume `𝒬 ⊆ {q ≥ 0 | 𝟏⊤q = 1}`, `z̲ᵏ ≤ µᵏ ≤ z̄ᵏ` and `δᵏ ≥ 0` for every `k`, and `g(x, ·) > −∞`.
Then both equalities hold, and when `𝒬 ≠ ∅` both outer suprema are attained by one `q ∈ 𝒬`
(the paper's "max").

**Formalization Note** `𝓕` is the set of joint laws of `(k̃, z̃)` of `ambiguitySet` (conditional
constraints multiplied by `q_k`), so the first equality is a disintegration over the finite `k̃`,
not a definition. In the middle expression the inner supremum runs over families `(ℙᵏ)_{k∈[K]}` with
`ℙᵏ ∈ 𝓕ᵏ` for every `k`. Products and sums are in `EReal`, with `0 · ∞ = 0`. The hypothesis
`g(x, ·) > −∞` follows from the paper's standing assumption that Problem (2) has a finite value. -/
theorem scenario_decomposition {l m r n K s : ℕ} (D : Data l m r n K s)
    (hQ : ∀ q ∈ QSet D.R D.ν, (∀ k, 0 ≤ q k) ∧ ∑ k, q k = 1)
    (hR : ∀ k, D.zl k ≤ D.μ k ∧ D.μ k ≤ D.zu k ∧ 0 ≤ D.δ k) (x : Fin l → ℝ)
    (hbot : ∀ z, D.g x z ≠ ⊥) :
    worstCaseCost D x =
        ⨆ q ∈ QSet D.R D.ν, ⨆ (Pk : Fin K → Measure (Fin n → ℝ))
          (_ : ∀ k, Pk k ∈ scenarioSet (D.μ k) (D.δ k) (D.zl k) (D.zu k)),
          ∑ k, ((q k : ℝ) : EReal) * DupacovaWets.Consistency.expect (Pk k) (D.g x) ∧
      worstCaseCost D x =
        ⨆ q ∈ QSet D.R D.ν,
          ∑ k, ((q k : ℝ) : EReal) * scenarioWorstCase (D.g x) (D.μ k) (D.δ k) (D.zl k) (D.zu k) ∧
      ((QSet D.R D.ν).Nonempty → ∃ q ∈ QSet D.R D.ν,
        worstCaseCost D x =
          (⨆ (Pk : Fin K → Measure (Fin n → ℝ))
            (_ : ∀ k, Pk k ∈ scenarioSet (D.μ k) (D.δ k) (D.zl k) (D.zu k)),
            ∑ k, ((q k : ℝ) : EReal) * DupacovaWets.Consistency.expect (Pk k) (D.g x)) ∧
        worstCaseCost D x =
          ∑ k, ((q k : ℝ) : EReal) *
            scenarioWorstCase (D.g x) (D.μ k) (D.δ k) (D.zl k) (D.zu k)) := by sorry

end SupermodDRO
