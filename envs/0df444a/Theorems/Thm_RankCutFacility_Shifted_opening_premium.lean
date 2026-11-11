-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_opening_premium
-- name    : RankCutFacility.Shifted.opening_premium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:58.629178+00:00
-- url     : https://prove2.me/theorems/6f86f96b-d783-44f9-b8a8-2b82e4ce46d3
-- title:
--   Lemma 4.3 — One-request opening premium and envelope identity
-- statement:
--   Let $(M,d)$ be any metric space, with finite nonempty ordered candidate set $F$, positive real opening costs $f_y$, and current nonempty open set $O$. Fix an arriving location $x$, a finite real upper bound $B\ge d(x,O)$, and penalty $\beta\in(0,1]$. The charge is computed by the same single-request rule as Algorithm 1; $\phi_\alpha(x)=\min_{y\in F}(d(x,y)+\alpha f_y)$.
--
--   Lemma 4.3. Fix a request x and an upper bound B on its pre-service connection distance. For each candidate y, let Pᵧ = (B − d(x, y))⁺ be its possible connection saving relative to B. Apply Lemma 4.1 to the cost–saving pairs (fᵧ, Pᵧ) together with the origin, and let wᵢ and xᵢ be the resulting cost increments and switching penalties. If the request is processed with penalty β ∈ (0, 1], then
--   $$
--   \operatorname{ALG}(x)\le B+(1-\beta)\sum_iw_i\mathbf1\{\beta\le x_i\}.\tag{12}
--   $$
--   Moreover,
--   $$
--   \sum_iw_i(x_i-\alpha)^+=(B-\phi_\alpha(x))^+\qquad(0\le\alpha\le1).\tag{13}
--   $$
--
--   This controls a later request without assuming any envelope identity as a hypothesis.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: finite switching lists and inclusive indices 1 through m → functions on Fin m or edge indices 0 through m-1; reason: this reindexes every summand and retains the empty-list case and non-strict switch tests
--   - encoding: finite B bounds the pre-service distance, where empty-set distance is infinite → the current open set is explicitly nonempty; reason: a finite upper bound excludes the empty state in the source
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.3, printed p. 10 (PDF p. 12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem opening_premium {M : Type*} [MetricSpace M] (G : Geometry M)
    (O : Finset (Fin G.m)) (hO : O.Nonempty) (x : M) (B β : ℝ)
    (hB : connection G O x ≤ B) (hβ : 0 < β ∧ β ≤ 1) :
    (serviceCost G O β x ≤ B + (1-β) *
      ∑ i ∈ Finset.range (edgeCount (savingPairs G x B)),
        if β ≤ switch (savingPairs G x B) i then weight (savingPairs G x B) i else 0)
    ∧ (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      (∑ i ∈ Finset.range (edgeCount (savingPairs G x B)),
        weight (savingPairs G x B) i * positivePart (switch (savingPairs G x B) i - α)) =
      positivePart (B - phi G α x)) := by sorry
end RankCutFacility.Shifted
