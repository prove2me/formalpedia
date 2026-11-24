-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_Supplement_theorem_3_2
-- name    : RankAssort.SimpleLearn.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:24:49.2919+00:00
-- url     : https://prove2.me/theorems/fa2e6525-374c-4eca-b880-9a842a0d894b
-- title:
--   Theorem 3 (2), p. 22 — under OnAR with Independence, w.p. 1 − δ the Simple Learning ranking hooks (1 − 1/e) of the optimum minus ϵ
-- statement:
--   Customer types $(p,f,k)$ are drawn i.i.d. from an unknown distribution $\mathcal D$, and $\mathbb E[H(\pi)]$ is the probability that a customer is hooked by the ranking $\pi$. Assume **OnAR with Independence**: $p$, $f$ and $k$ are pairwise independent under $\mathcal D$. Let $\epsilon,\delta>0$. Run the Simple Learning Algorithm (Algorithm 2) with an $(\epsilon',\delta')$-PAC algorithm as a black box, where
--   $$\epsilon'=\frac{2\epsilon}{n},\qquad\delta'=\frac{\delta}{n}.$$
--   Then, with probability at least $1-\delta$ over the learning randomness, the returned ranking $\tilde\pi$ satisfies, for every ranking $\pi^*$ of the $n$ products,
--   $$\mathbb E[H(\tilde\pi)]\ \ge\ \Big(1-\frac1e\Big)\mathbb E[H(\pi^*)]-\epsilon.$$
--
--   This is the online counterpart of Theorem 2, and the independent-types companion of the mission's goal (Theorem 3, part 1), which gives the ratio $\tfrac12$ without independence.
--
--   **Formalization Note** The hypotheses copy the published goal `RankAssort.SimpleLearn.theorem_3_1` exactly, `SimpleLearningRun D τ (2ϵ/n) (δ/n) P`: at every rank, conditionally on every prefix, the black box picks a product that is not $2\epsilon/n$-best among the unranked products with probability at most $\delta/n$. Only the three pairwise independence hypotheses are added. The paper omits the proof ("follows in an almost identical fashion", pp. 57–58).
--
--   Differences from the source:
--   - reading: any (ϵ′, δ′)-PAC algorithm as a black box → the per-rank, prefix-conditional PAC guarantee SimpleLearningRun D τ (2ϵ/n) (δ/n) P of the published goal; reason: Definition 1 (p. 21) applied at each rank to the marginal-benefit arms given the prefix, as used on p. 58; identical to the published Theorem 3, part 1
--   - reading: π∗ the optimal ranking (optimal solution to OffAR) → every full ranking π∗ (duplicate-free, length n); reason: the optimum is attained among finitely many full rankings, so a bound against every full ranking is equivalent to the bound against the optimum; same reading as the published goal
--   - encoding: pₜ, fₜ and kₜ are all pairwise independent → three IndepFun hypotheses under D for θ ↦ p, θ ↦ f, θ ↦ k (product σ-algebras on Fin n → ℝ and Fin n → Finset (Fin n) → ℝ, ⊤ on ℕ); reason: literal pairwise independence; D is not assumed to be a product measure
--   - encoding: types drawn from an arbitrary distribution D → a probability measure D on a measurable type space Θ and a type map τ with TypeMeasurable τ; reason: as in every published base item: without measurability the expectations ∫ … ∂D would be junk zeros; the paper's expectations presuppose it
--   - encoding: with probability (1 − δ) → ENNReal.ofReal (1 − δ) ≤ P{ω | …}; reason: 'with probability 1 − δ' is read as 'at least 1 − δ', as in the published goal; ofReal makes the bound vacuous for δ ≥ 1
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 22, Theorem 3 (2); p. 19 (OffAR/OnAR with Independence); p. 21, Definition 1; p. 23, Algorithm 2

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Algorithm

namespace RankAssort.SimpleLearn.Supplement
open MeasureTheory ProbabilityTheory

/-- Theorem 3, part 2 (p. 22). Under OnAR with Independence (`p`, `f` and `k` pairwise independent
under `D`), the Simple Learning Algorithm driven by a `(2ϵ/n, δ/n)`-PAC black box returns, with
probability at least `1 − δ`, a ranking `π̃` with `E[H(π̃)] ≥ (1 − 1/e) E[H(π∗)] − ϵ` for every full
ranking `π∗`. -/
theorem theorem_3_2 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (hpf : IndepFun (fun θ => (τ θ).p) (fun θ => (τ θ).f) D)
    (hpk : IndepFun (fun θ => (τ θ).p) (fun θ => (τ θ).k) D)
    (hfk : IndepFun (fun θ => (τ θ).f) (fun θ => (τ θ).k) D)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ (2 * eps / n) (delta / n) P) :
    ENNReal.ofReal (1 - delta) ≤
      P {ω | ∀ piStar : List (Fin n), piStar.Nodup → piStar.length = n →
              (1 - Real.exp (-1)) * expHook D τ piStar - eps ≤ expHook D τ (run.out ω)} := by sorry

end RankAssort.SimpleLearn.Supplement
