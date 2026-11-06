-- Prove2me | Theorems.Thm_PlanningProphet_uniform_mixture
-- name    : PlanningProphet.uniform_mixture
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:35.822377+00:00
-- url     : https://prove2.me/theorems/dacfec2d-65b8-43c5-b357-214f13742e40
-- title:
--   §4.1, pp.12–13 — choosing one of $k$ policies uniformly at random averages their values
-- statement:
--   Let $k\ge1$ and let $\pi_1,\dots,\pi_k$ be online policies on a graph $G$ with seed laws $\nu_1,\dots,\nu_k$. Suppose each $\pi_i$ always selects a feasible $s,t$-path and its selected path is a random variable. Let the values $W$ be a measurable random vector under a probability measure $\mu$. Then there is an online policy $\pi'$ on $G$ with these two properties such that
--   $$\mathbb E(ALG_{\pi'})=\frac1k\sum_{i=1}^k \mathbb E(ALG_{\pi_i}).$$
--
--   The policy $\pi'$ chooses $i$ uniformly at random, independently of the values, and then runs $\pi_i$. In the proof of Theorem 4, this gives $\mathbb E(ALG)\ge\frac1k\sum_{i=1}^k\frac1{d+2}\,\mathbb E(OPT(G_i))$.
--
--   Differences from the source:
--   - encoding: a finite graph and a finite label set $L$ → `[Fintype V] [Fintype E] [Fintype L]`, with `V E L : Type`; reason: finite data; every finite type is equivalent to one in `Type`
--   - encoding: non-negative random values $w_e$ and expectations $\mathbb E(\cdot)$ → a measurable `W : Ω → E → ℝ≥0` on a probability space $(\Omega,\mu)$; expectations are lower Lebesgue integrals in `ℝ≥0∞`; reason: for non-negative values the lower integral is the expectation, finite or infinite; no integrability hypothesis is needed
--   - reading: an algorithm or policy $ALG$ that determines at each node which edge to follow next, given the observed realizations so far, where $w_e$ is observed when the tail of $e$ is reached → an `OnlinePolicy` with a seed space $\Xi$ and seed law $\nu$: the decision reads $w$ only on edges leaving visited nodes; the seed is independent of the values (expectation under $\nu\otimes\mu$); the run is a label-feasible $s,t$-path for every seed and value vector; the run is cut off after $|V|$ steps; reason: the model of p.6; the algorithms of pp.8–12 are randomized, their coins drawn independently of everything else; an $s,t$-path of a DAG has fewer than $|V|$ edges
--   - reading: $\mathbb E(ALG)$, an expectation → an extra conjunct: the selected path is a random variable (`RunMeasurable`: each event $\{ALG\text{ selects }p\}$ is measurable); reason: an expectation presupposes a random variable; the conjunct only strengthens the conclusion
--   - generalization: the $k$ algorithms obtained from Theorem 3 on $G_1,\dots,G_k$, run in a covered DAG → any $k$ online policies on any graph whose runs are feasible $s,t$-paths and random variables; reason: those $k$ algorithms are such policies
--   - reading: $\mathbb E(ALG)\ge\frac1k\sum_i\frac1{d+2}\mathbb E(OPT(G_i))$ for the uniform choice → $\mathbb E(ALG_{\pi'})=\frac1k\sum_i\mathbb E(ALG_{\pi_i})$; reason: the paper's inequality follows by bounding each $\mathbb E(ALG_{\pi_i})$ with Theorem 3 and `focal_simulation`
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §4.1 Proof of Theorem 4, pp.12–13, "Consider the algorithm that chooses uniformly at random one of the instances G1, …, Gk" and the display on p.13

import Mathlib
import Definitions.Def_PlanningProphet_OnlinePolicy

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **Choosing one of `k` policies uniformly at random** (Cristi–Oren, arXiv:2406.13911v1, §4.1,
pp.12–13). "Consider the algorithm that chooses uniformly at random one of the instances
`G₁, …, G_k`. Let this be `Gᵢ`. Then, it runs the algorithm given by Theorem 3 on `Gᵢ`." and
(p.13) `E(ALG) ≥ 1/k · Σ_{i=1}^k 1/(d+2) · E(OPT(Gᵢ))`.

For `k ≥ 1` online policies `π₁, …, π_k` on `G` with seed laws `ν₁, …, ν_k`, each run always a
label-feasible `s,t`-path and a random variable, there is an online policy on `G` (one that first
picks `i` uniformly at random, independently of the values, then runs `πᵢ`) with the same two
properties and `E(ALG) = (1/k) Σᵢ E(ALGᵢ)`. -/
theorem uniform_mixture {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) {k : ℕ} (hk : 1 ≤ k)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → E → ℝ≥0) (hW : Measurable W)
    (Ξ : Fin k → Type u) [∀ i, MeasurableSpace (Ξ i)] (ν : ∀ i, Measure (Ξ i))
    [∀ i, IsProbabilityMeasure (ν i)] (π : ∀ i, OnlinePolicy G (Ξ i))
    (hπ : ∀ i, (π i).IsFeasibleRun) (hπm : ∀ i, (π i).RunMeasurable W) :
    ∃ (Ξ' : Type u) (_ : MeasurableSpace Ξ') (ν' : Measure Ξ') (π' : OnlinePolicy G Ξ'),
      IsProbabilityMeasure ν' ∧ π'.IsFeasibleRun ∧ π'.RunMeasurable W ∧
      π'.expectedAlg ν' μ W = 1 / (k : ℝ≥0∞) * ∑ i, (π i).expectedAlg (ν i) μ W := by sorry

end PlanningProphet
