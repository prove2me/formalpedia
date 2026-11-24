-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_Supplement_theorem_2
-- name    : RankAssort.SimpleLearn.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:24:07.525971+00:00
-- url     : https://prove2.me/theorems/b6deaa77-51bb-4d06-bb38-44771e958aaa
-- title:
--   Theorem 2 — under pairwise independence of p, f, k every greedy ranking hooks at least (1 − 1/e) of the optimum
-- statement:
--   Let $\mathcal D$ be a distribution of customer types $(p,f,k)$ over $n$ products: click probabilities $p_i\in[0,1]$, bias functions $f_i$ with $f_i(\emptyset)=0$, and a first impression window $1\le k\le n$. Write $\mathbb E[H(\pi)]$ for the probability that a random customer is hooked by $\pi$, i.e. clicks some product among her first $k$ ranks under the sequential click law with bias. Assume **OffAR with Independence**: $p$, $f$ and $k$ are pairwise independent under $\mathcal D$.
--
--   Let $\pi^g$ be any output of the Greedy Algorithm for OffAR (Algorithm 1): for $r=1,\dots,n$ it places at rank $r$ an unranked product $i$ maximizing the marginal benefit $\mathbb E[H([\pi^g]_{r-1}\cup i)-H([\pi^g]_{r-1})]$, with ties broken arbitrarily. Then for every ranking $\pi^*$ of the $n$ products,
--   $$\mathbb E[H(\pi^g)]\ \ge\ \Big(1-\frac1e\Big)\,\mathbb E[H(\pi^*)].$$
--
--   Without independence the greedy algorithm is only a $\tfrac12$-approximation (Theorem 1). Under independence the ratio improves to the classical $1-1/e$, the guarantee also obtained in the online setting by Theorem 3, part 2.
--
--   **Formalization Note** The greedy output is a duplicate-free list `l` of length $n$ such that at every 0-based rank $r$ the product `l[r]` satisfies the published `IsApproxBest D τ (l.take r) (l[r]) 0`: it is unranked and its marginal benefit is at least that of every unranked product. These are exactly the outputs of Algorithm 1 under all tie-breakings. $1-1/e$ is `1 - Real.exp (-1)`.
--
--   Differences from the source:
--   - reading: the Greedy Algorithm achieves a (1 − 1/e)-approximation factor → for every greedy output (every tie-breaking of the arg max) and every full ranking π∗, (1 − e⁻¹)·E[H(π∗)] ≤ E[H(πg)]; reason: an approximation factor compares with the optimum, attained among the finitely many full rankings; the page does not fix a tie-breaking rule
--   - encoding: pₜ, fₜ and kₜ are all pairwise independent → three IndepFun hypotheses under D for θ ↦ p, θ ↦ f, θ ↦ k (product σ-algebras on Fin n → ℝ and Fin n → Finset (Fin n) → ℝ, ⊤ on ℕ); reason: literal pairwise independence; D is not assumed to be a product measure
--   - encoding: types drawn from an arbitrary distribution D → a probability measure D on a measurable type space Θ and a type map τ with TypeMeasurable τ; reason: as in every published base item: without measurability the expectations ∫ … ∂D would be junk zeros; the paper's expectations presuppose it
--   - encoding: Algorithm 1's output πg → a duplicate-free list of length n with IsApproxBest … 0 at every 0-based rank; reason: exactly the set of outputs of Algorithm 1; ranks are 0-based in Lean
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 19, Theorem 2; p. 17, Algorithm 1; p. 19 (OffAR with Independence)

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Algorithm

namespace RankAssort.SimpleLearn.Supplement
open MeasureTheory ProbabilityTheory

/-- Theorem 2 (p. 19). Under OffAR with Independence (`p`, `f` and `k` pairwise independent
under `D`), every output `l` of the Greedy Algorithm for OffAR (Algorithm 1, every tie-breaking of
its arg max: at each 0-based rank `r` the product `l[r]` is unranked and has maximum marginal
benefit among the unranked products) satisfies `E[H(l)] ≥ (1 − 1/e) E[H(π∗)]` for every full
ranking `π∗`. -/
theorem theorem_2 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (hpf : IndepFun (fun θ => (τ θ).p) (fun θ => (τ θ).f) D)
    (hpk : IndepFun (fun θ => (τ θ).p) (fun θ => (τ θ).k) D)
    (hfk : IndepFun (fun θ => (τ θ).f) (fun θ => (τ θ).k) D)
    (l : List (Fin n)) (hl : l.Nodup) (hllen : l.length = n)
    (hgreedy : ∀ r < n, ∃ i, l[r]? = some i ∧ IsApproxBest D τ (l.take r) i 0)
    (piStar : List (Fin n)) (hs : piStar.Nodup) (hslen : piStar.length = n) :
    (1 - Real.exp (-1)) * expHook D τ piStar ≤ expHook D τ l := by sorry

end RankAssort.SimpleLearn.Supplement
