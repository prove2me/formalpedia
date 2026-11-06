-- Prove2me | Theorems.Thm_ParetoNCSched_lemma_B_2
-- name    : ParetoNCSched.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:24:46.620884+00:00
-- url     : https://prove2.me/theorems/4aa335c9-48c1-4c8d-99a6-61d3cf5e62ed
-- title:
--   Lemma B.2 — growth rate $a\gamma_c+(1-a)\gamma_r$ of $\Phi$
-- statement:
--   Let $R\ge2$ and consider the state of the run of $\mathrm{MRC}_R$ at a time $t<t_\infty$ with $N(t)\ge2$, committed job $j$. Suppose that, from this state, $j$ runs at rate $a$ and each waiting job at rate $b=\frac{1-a}{N-1}$ (completed jobs at rate $0$), where $\frac1N\le a\le1$. Then $u\mapsto\Phi(e(t)+u\,r)$ has right derivative at $u=0$
--   $$a\,\gamma_c+(1-a)\,\gamma_r .$$
--   In particular, committing ($a=1$) makes $\Phi$ grow at rate $\gamma_c$.
--
--   This is the rate computation behind the branch rule of Algorithm 1: the mixing rate $a$ is chosen so that $\Phi$ grows at exactly $N/R$.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: "at every time t < t∞" → "t ∈ [t_k, t_{k+1}) for some k"; reason: t₀ = 0 and the event times are non-decreasing, so the union of these intervals is [0, t∞)
--   - encoding: "Φ(e(t)) has right derivative aγ_c + (1 − a)γ_r" under the hypothetical rates → the derivative within [0, ∞) at 0 of u ↦ Φ(e(t) + u·r_a); reason: the right derivative of Φ along the constant-rate continuation of the state
--   - encoding: "In particular, committing (a = 1) makes Φ grow at rate γ_c" → the instance a = 1 of the main statement, not stated separately; reason: a = 1 satisfies 1/N ≤ a ≤ 1
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
--   - encoding: N(t) = |{j : C_j > t}| (p.15) at a time t → #{i : eᵢ(t) < pᵢ}, the unfinished jobs of the state ⟨t, e(t), F(t)⟩ (`stateAt`); reason: p.17: a job is completed iff eᵢ = pᵢ; on the run eᵢ is continuous and non-decreasing, so eᵢ(t) < pᵢ iff Cᵢ > t
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma B.2, p.18

import Mathlib
import Definitions.Def_ParetoNCSched_stateAt
import Definitions.Def_ParetoNCSched_committedJob
import Definitions.Def_ParetoNCSched_gammaC
import Definitions.Def_ParetoNCSched_gammaR
import Definitions.Def_ParetoNCSched_mixRates
import Definitions.Def_ParetoNCSched_eventTime
import Definitions.Def_ParetoNCSched_Phi
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Lemma B.2 (Growth rate of Φ).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, Lemma B.2, p.18: "Consider the state of the
run at a time t < t∞ with N(t) ≥ 2. Suppose that, from this state, j runs at rate a and each waiting
job at rate b = (1−a)/(N−1), where 1/N ≤ a ≤ 1. Then Φ(e(t)) has right derivative aγ_c + (1 − a)γ_r.
In particular, committing (a = 1) makes Φ grow at rate γ_c." Standing assumption (p.17): R ≥ 2.

**Formalization Note.** "t < t∞" is `t ∈ [t_k, t_{k+1})`; the right derivative is the derivative
within `[0, ∞)` at `0` of `u ↦ Φ(e(t) + u·r_a)`, where `r_a` gives `a` to `j`, `(1−a)/(N−1)` to each
waiting job and `0` to completed jobs. The "in particular" is the instance `a = 1`. -/
theorem lemma_B_2 (R : ℝ) (hR : 2 ≤ R) {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Equiv.Perm (Fin n)) (k : ℕ) (t : ℝ)
    (ht : t ∈ Ico (eventTime R p σ k) (eventTime R p σ (k + 1)))
    (hN : 2 ≤ (unfinished p (stateAt R p σ t)).card)
    (j : Fin n) (hj : committedJob p σ (stateAt R p σ t) = some j)
    (a : ℝ) (ha₁ : 1 / ((unfinished p (stateAt R p σ t)).card : ℝ) ≤ a) (ha₂ : a ≤ 1) :
    HasDerivWithinAt
      (fun u : ℝ => Phi ((stateAt R p σ t).e + u • mixRates p (stateAt R p σ t) j a))
      (a * gammaC (stateAt R p σ t) j + (1 - a) * gammaR p (stateAt R p σ t) j) (Ici 0) 0 := by sorry

end ParetoNCSched
