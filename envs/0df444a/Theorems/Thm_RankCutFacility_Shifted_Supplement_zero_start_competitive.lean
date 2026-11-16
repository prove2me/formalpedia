-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_zero_start_competitive
-- name    : RankCutFacility.Shifted.Supplement.zero_start_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:22.599536+00:00
-- url     : https://prove2.me/theorems/5cc64016-f636-4bdb-9ee4-bf6be7c92388
-- title:
--   Theorem B.1 — Algorithm 2 satisfies $\mathbb E[\mathrm{ALG}]\le\max\{\Phi(\mu),3+2\mu\}\mathrm{OPT}$
-- statement:
--   Algorithm 2 (Zero-Start Candidate Marginal DistCut) serves requests in a metric space with a prescribed finite candidate set of unit opening costs. At rank $t$ it computes $D=d(x,O_{t-1})$ ($+\infty$ if nothing is open), $a=d(x,F)$, $\Delta=D-\min\{D,a\}$ and $z_t=(t-1)/n$; it opens a fixed nearest candidate iff $\Delta\ge\theta_\mu(z_t)=\min\{1,z_t/\mu\}$ and connects $x$ to its nearest open facility.
--
--   **Theorem B.1.** For every $\mu\in(0,1]$, every horizon $n\ge1$ and every demand multiset, Algorithm 2 satisfies
--
--   $$\mathbb E[\mathrm{ALG}]\le\max\{\Phi(\mu),3+2\mu\}\,\mathrm{OPT},\qquad\Phi(\mu)=1+\frac{e^{-(1+\mu)}}{\mu},$$
--
--   with the expectation over the uniformly random arrival order.
--
--   At the balancing parameter $\mu^*$ this gives ratio $C^*<3.281$ for unit costs on prescribed sites.
--
--   Differences from the source:
--   - encoding: Algorithm 2 with a fixed nearest-candidate tie-breaking rule → zeroStartStep: open the first nearest candidate in the enumeration iff O = ∅ or θ_μ((t−1)/n) ≤ (d(x,O) − d(x,F))^+, then connect to the nearest open facility; reason: the branch O = ∅ is the source's Δ = +∞ case; the enumeration order is the fixed tie-breaking rule
--   - encoding: unit opening costs on a prescribed finite candidate set → the published Geometry with the hypothesis that every fee equals 1; reason: this is the Appendix B setting; the ambient metric remains arbitrary
--   - encoding: Φ(µ) → the published limitingA µ; reason: both are 1 + e^{-(1+µ)}/µ
--   - encoding: a multiset of n demand copies → a map u : Fin n → M (repeated locations allowed); reason: labels distinguish repeated copies for permutation ranks and never enter an online decision
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
--   - encoding: every horizon n, including n = 0 (empty multiset, ALG = OPT = 0) → the upper-bound clauses assume 0 < n; reason: at n = 0 the source's bound reads 0 ≤ 0, while the published optimum minimizes over nonempty facility sets; the hypothesis excludes only this degenerate horizon
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem B.1, printed p. 31 (PDF p. 33)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Runs

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-- Theorem B.1 (PDF p. 33, printed p. 31): for every `µ ∈ (0,1]`, Algorithm 2 on unit-cost
prescribed candidates satisfies `E[ALG] ≤ max{Φ(µ), 3 + 2µ} · OPT`. -/
theorem zero_start_competitive {M : Type*} [MetricSpace M] (G : Geometry M)
    (hunit : ∀ y, G.fee y = 1) {n : ℕ} (hn : 0 < n) (u : Fin n → M) (μ : ℝ)
    (hμ : 0 < μ ∧ μ ≤ 1) :
    uniformAvg (zeroStartAlg G u μ) ≤ max (limitingA μ) (3 + 2 * μ) * optimum G u := by sorry

end RankCutFacility.Shifted.Supplement
