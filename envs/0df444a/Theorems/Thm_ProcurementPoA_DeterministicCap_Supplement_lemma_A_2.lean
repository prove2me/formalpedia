-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_lemma_A_2
-- name    : ProcurementPoA.DeterministicCap.Supplement.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T17:39:19.58464+00:00
-- url     : https://prove2.me/theorems/4a4bbe86-62ae-4ddf-bdd2-cf954f0d87e4
-- title:
--   Lemma A.2 — On the rival instance I_n(m,θ), every acceptance function that is regular or vanishes above 1 admits a tie-free BNE without underbiddin
-- statement:
--   Let $0<m<R-1$, $0<\theta<1$ and $n\ge1$. In the rival instance $I_n(m,\theta)$ there are $n+1$ suppliers: supplier $0$ has cost $1$, and each rival independently has cost $1+m$ with probability $1-\theta^{1/n}$ and cost $R$ otherwise. Let $S$ be any acceptance function for $R$ that is regular or vanishes at every bid above $1$, and write $\pi=\pi(1)$. For every measurable lowest-bid tie rule there exists a mixed no-underbidding Bayes–Nash equilibrium with almost surely pairwise distinct real bids, $\mathrm{SC}_{\mathrm{OPT}}=1$, and
--   $$\mathrm{SC}-\mathrm{SC}_{\mathrm{OPT}}\ge\theta^{1/n}\Phi_{m,\theta}(\pi),\qquad
--   \Phi_{m,\theta}(p)=\begin{cases}m(1-\theta)(1-m/(\theta p)),&\theta p>m,\\0,&\theta p\le m.\end{cases}$$
--   In addition, $\Phi_{m,\theta}$ is nondecreasing on $\mathbb R$, concave on $[m/\theta,\infty)$, and
--   $$\lim_{p\to\infty}\Phi_{m,\theta}(p)=(1-\theta)m.$$
--   The finite-$n$ factor is retained. This is the fixed rival instance used by the regular-mechanism lower bound, and all three properties of its loss function are included.
--
--   Differences from the source:
--   - encoding: independent private costs, mixed used bids and arbitrary tie rules → Fin (n+1) suppliers, Borel type laws, Markov bid and tie kernels, and typewise incentives almost everywhere in the drawn bid; reason: covers every nonempty finite population and cost atoms using the published model; used bids are interpreted probabilistically rather than as topological support endpoints
--   - reading: the auction has an equilibrium without ties → there is such an equilibrium for every measurable lowest-bid tie rule; reason: §2 says tie rules matter only for Remark 4.2; the proof on PDF 21 bounds deviations independently of tie resolution
--   - encoding: SC − SCOPT ≥ the nonnegative rival loss → SCOPT + ofReal(θ^(1/n) Φ(π)) ≤ SC, with SCOPT = 1 explicitly; reason: finite positive costs make this equivalent and avoid truncated extended-real subtraction
--   - encoding: without ties among real bids → pairwise distinct suppliers bids almost surely under the full type-and-bid law; reason: the construction has continuous competing bids and distinct above-R bids; the phantom bid is not counted
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Lemma A.2, printed p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Monopoly
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_RivalInstance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- Rival equilibrium with its finite-n loss, tie freedom, and all three properties of Φ. -/
theorem lemma_A_2 (R m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n)
    (S : ℝ → ℝ) (hS : IsAcceptance R S)
    (hreg : IsRegular R S ∨ ∀ b : ℝ, 1 < b → S b = 0) (τ : TieRule n) :
    (∃ σ : MixedProfile n,
      IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ σ S ∧
      NoBidTies (rivalInstance R m θ n hθ.le hθ1.le) σ ∧
      optimalSocialCost (rivalInstance R m θ n hθ.le hθ1.le) = 1 ∧
      optimalSocialCost (rivalInstance R m θ n hθ.le hθ1.le) +
        ENNReal.ofReal (rivalHighProbability θ n * Phi m θ (monopolyProfit S 1)) ≤
      acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ σ R S) ∧
    Monotone (Phi m θ) ∧
    ConcaveOn ℝ (Set.Ici (m / θ)) (Phi m θ) ∧
    Tendsto (Phi m θ) atTop (𝓝 ((1 - θ) * m)) := by sorry

end ProcurementPoA.DeterministicCap.Supplement
