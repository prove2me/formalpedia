-- Prove2me | Theorems.Thm_SemiBanditSOO_lemma_5_4_b
-- name    : SemiBanditSOO.lemma_5_4_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:34.312464+00:00
-- url     : https://prove2.me/theorems/df1aa975-50ce-406a-94a6-dabbda6c9c52
-- title:
--   Lemma 5.4(b) — $|\mathbb E_Q\phi-\mathbb E_P\phi|\le24\sqrt{\frac{s\Lambda\log(m+1)}{m+1}\mathrm{Var}_P\phi}+\frac{417s\Lambda}{m+1}$ for level-set complexity $\le s$
-- statement:
--   Let $s\ge1$ and $m\ge0$ be integers and $P,Q\in\mathcal C_m(\widehat D_{i,m})$. For every measurable $[0,1]$-valued function $\phi$ with level-set complexity at most $s$,
--   $$\bigl|\mathbb E_{X\sim Q}[\phi(X)]-\mathbb E_{X\sim P}[\phi(X)]\bigr|\le24\sqrt{\frac{s\Lambda\log(m+1)}{m+1}\mathrm{Var}_{X\sim P}(\phi(X))}+\frac{417s\Lambda}{m+1}.$$
--
--   This is the bound that controls the gap between an optimistic value and the true expectation when the continuation value has small level-set complexity.
--
--   **Formalization Note.** As in Lemma 5.4(a); $m=0$ is allowed, in which case $\mathcal C_0$ is the set of all distributions on the domain.
--
--   Differences from the source:
--   - encoding: D̂_{i,m}, the empirical distribution of the first m revealed values of coordinate i → the empirical frequency of an arbitrary list L of m points of the domain; reason: the lemma is used for every sample; only the values of the sample enter
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: Λ, the quantity of §3.1 → Lam n T δ = log(80n(T + 1)³/δ) with 1 ≤ n, 1 ≤ T, δ ∈ (0, 1) as binders; reason: Λ is defined from n, T, δ on p.9
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Lemma 5.4(b), p.21

import Mathlib
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet

open MeasureTheory

namespace SemiBanditSOO

/-- **Lemma 5.4(b) (functions of small level-set complexity).** Harada, Kawase, Sumita, *Beyond
Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1,
Lemma 5.4(b), p.21.

Let `s ≥ 1` and `m ≥ 0` be integers and `P, Q ∈ 𝒞_m(D̂_{i,m})`. For every measurable `[0, 1]`-valued
function `ϕ` with level-set complexity at most `s`,
`|𝔼_{X∼Q}[ϕ(X)] − 𝔼_{X∼P}[ϕ(X)]| ≤ 24 √(sΛ log(m + 1)/(m + 1) · Var_{X∼P}(ϕ(X))) + 417 sΛ/(m + 1)`.

**Formalization Note.** As in Lemma 5.4(a); `m = 0` is allowed, in which case `𝒞_0` is the set of
all distributions on the domain. -/
theorem lemma_5_4_b {dom : Set ℝ} (hdom : dom ⊆ Set.Icc 0 1) (n T : ℕ) (δ : ℝ) (hn : 1 ≤ n)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1) (s : ℕ) (hs : 1 ≤ s) (L : List dom)
    (P Q : ProbabilityMeasure dom) (hP : P ∈ confSet (Lam n T δ) L)
    (hQ : Q ∈ confSet (Lam n T δ) L) (ϕ : dom → ℝ) (hϕ : Measurable ϕ)
    (hϕ01 : ∀ z, ϕ z ∈ Set.Icc (0 : ℝ) 1) (hcpx : LevelSetCpxLE (s : ℕ∞) ϕ) :
    |∫ z, ϕ z ∂(Q : Measure dom) - ∫ z, ϕ z ∂(P : Measure dom)| ≤
      24 * Real.sqrt (s * Lam n T δ * Real.log (L.length + 1) / (L.length + 1) *
          ProbabilityTheory.variance ϕ (P : Measure dom)) +
        417 * s * Lam n T δ / (L.length + 1) := by sorry

end SemiBanditSOO
