-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_zero_start_later_request
-- name    : RankCutFacility.Shifted.Supplement.zero_start_later_request
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:15.188214+00:00
-- url     : https://prove2.me/theorems/bf8e8d1d-c922-4764-bfa1-2685d97d309e
-- title:
--   Lemma B.2 — Later-request bound for Algorithm 2 with signed baseline correction
-- statement:
--   Run Algorithm 2 (unit costs on a prescribed finite candidate set, zero-start clock $z_t=(t-1)/n$, threshold $\theta_\mu(z)=\min\{1,z/\mu\}$) with $\mu\in(0,1]$. Fix an optimal cluster $C$, let $p$ be its first copy in the random permutation, $D_p$ the connection distance paid after serving $p$, and $a_u=d(u,F)$. Let $K_p$ be the observed history through the service of $p$ (the ordered prefix of requests through $p$), and $\mathrm{ALG}(u)$ the opening plus connection cost charged to the round of $u$.
--
--   **Lemma B.2.** For every fixed demand copy $u\in C$, on the event $u\ne p$,
--
--   $$\mathbb E[\mathrm{ALG}(u)\mid K_p]\le D_p+d(p,u)+\mu\big(a_p+d(p,u)-a_u\big).$$
--
--   The signed term may be negative; it cancels when averaged over the uniformly random first copy in Theorem B.1.
--
--   Differences from the source:
--   - encoding: conditional expectation given the observed history K_p through the service of p → the average over all arrival orders with the same ordered label prefix through the first rank of C; reason: for the deterministic Algorithm 2 that prefix determines the history through p, including p's identity, which the source treats as K_p-measurable; this is the published encoding of Lemma 4.5
--   - encoding: Algorithm 2 with a fixed nearest-candidate tie-breaking rule → zeroStartStep: open the first nearest candidate in the enumeration iff O = ∅ or θ_μ((t−1)/n) ≤ (d(x,O) − d(x,F))^+, then connect to the nearest open facility; reason: the branch O = ∅ is the source's Δ = +∞ case; the enumeration order is the fixed tie-breaking rule
--   - encoding: unit opening costs on a prescribed finite candidate set → the published Geometry with the hypothesis that every fee equals 1; reason: this is the Appendix B setting; the ambient metric remains arbitrary
--   - encoding: a fixed optimal solution and its clusters → Comparator together with IsOptimal (optimal, nearest assignment, no unused facility) and cluster Q c; reason: this is the published encoding of the standing assumptions of the cluster analysis
--   - encoding: a multiset of n demand copies → a map u : Fin n → M (repeated locations allowed); reason: labels distinguish repeated copies for permutation ranks and never enter an online decision
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Lemma B.2, printed p. 31 (PDF p. 33)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Runs

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-- Lemma B.2 (PDF p. 33, printed p. 31). Algorithm 2 with unit costs; `C` an optimal cluster,
`p` its first copy in `π`. Averaged over all arrival orders with the same ordered prefix through
the service of `p`, a later copy `a ∈ C` costs at most `D_p + d(p,a) + µ(a_p + d(p,a) − a_a)`. -/
theorem zero_start_later_request {M : Type*} [MetricSpace M] (G : Geometry M)
    (hunit : ∀ y, G.fee y = 1) {n : ℕ} (u : Fin n → M) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) (c : Fin G.m)
    (π : Arrival n) (p a : Fin n) (hp : anchor (cluster Q c) π = some p)
    (ha : a ∈ cluster Q c) (hne : a ≠ p) :
    avg (prefixFiber (cluster Q c) π) (fun σ => zsCopyCost G u μ σ a) ≤
      zsDistance G u μ π p + dist (u p) (u a) +
        μ * (candDist G (u p) + dist (u p) (u a) - candDist G (u a)) := by sorry

end RankCutFacility.Shifted.Supplement
