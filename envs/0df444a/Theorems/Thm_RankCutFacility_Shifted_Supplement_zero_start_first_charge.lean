-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_zero_start_first_charge
-- name    : RankCutFacility.Shifted.Supplement.zero_start_first_charge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:50.220316+00:00
-- url     : https://prove2.me/theorems/1750c65c-0813-4639-8233-377418872450
-- title:
--   Lemma B.3 — First-request charge $\mathbb E[L_p+k\varepsilon_p]\le\Phi(\mu)$
-- statement:
--   Run Algorithm 2 (unit costs, zero-start clock) with $\mu\in(0,1]$. For an optimal cluster $C$ of size $k$ let $p$ be its first copy in the uniformly random arrival order, $L_p\in\{0,1\}$ its opening cost, $D_p$ its post-service connection distance, $a_p=d(p,F)$ and $\varepsilon_p=(D_p-a_p)^+$.
--
--   **Lemma B.3.** For every cluster $C$ of size $k$,
--
--   $$\mathbb E[L_p+k\varepsilon_p]\le\Phi(\mu),\qquad \Phi(\mu)=1+\frac{e^{-(1+\mu)}}{\mu}.$$
--
--   The bound does not depend on $k$; it is the charge left at the first request after the later costs of Lemma B.2 are summed.
--
--   Differences from the source:
--   - encoding: E[L_p + kε_p] with p the first copy of C → uniform average over permutations of the anchor account of C applied to L_p + k(D_p − a_p)^+; reason: C is nonempty, so the anchor always exists and the average is the source's expectation
--   - encoding: Φ(µ) → the published limitingA µ; reason: both are 1 + e^{-(1+µ)}/µ
--   - encoding: Algorithm 2 with a fixed nearest-candidate tie-breaking rule → zeroStartStep: open the first nearest candidate in the enumeration iff O = ∅ or θ_μ((t−1)/n) ≤ (d(x,O) − d(x,F))^+, then connect to the nearest open facility; reason: the branch O = ∅ is the source's Δ = +∞ case; the enumeration order is the fixed tie-breaking rule
--   - encoding: unit opening costs on a prescribed finite candidate set → the published Geometry with the hypothesis that every fee equals 1; reason: this is the Appendix B setting; the ambient metric remains arbitrary
--   - encoding: a fixed optimal solution and its clusters → Comparator together with IsOptimal (optimal, nearest assignment, no unused facility) and cluster Q c; reason: this is the published encoding of the standing assumptions of the cluster analysis
--   - encoding: a multiset of n demand copies → a map u : Fin n → M (repeated locations allowed); reason: labels distinguish repeated copies for permutation ranks and never enter an online decision
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Lemma B.3, printed p. 32 (PDF p. 34)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Runs

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-- Lemma B.3 (PDF p. 34, printed p. 32). Algorithm 2 with unit costs; for every optimal cluster
`C` of size `k` with first copy `p`, `E[L_p + k ε_p] ≤ Φ(µ)`, where `ε_p = (D_p − a_p)^+`. -/
theorem zero_start_first_charge {M : Type*} [MetricSpace M] (G : Geometry M)
    (hunit : ∀ y, G.fee y = 1) {n : ℕ} (u : Fin n → M) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) (c : Fin G.m)
    (hC : (cluster Q c).Nonempty) :
    uniformAvg (fun π => anchorAccount (cluster Q c) π (fun p =>
        zsOpening G u μ π p +
          ((cluster Q c).card : ℝ) * positivePart (zsDistance G u μ π p - candDist G (u p)))) ≤
      limitingA μ := by sorry

end RankCutFacility.Shifted.Supplement
