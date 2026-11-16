-- Prove2me | Theorems.Thm_PottsRapidMixing_Supplement_theorem_1_3
-- name    : PottsRapidMixing.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:29:19.196197+00:00
-- url     : https://prove2.me/theorems/a95885d2-1dcc-414f-888f-7b3e1f6ffef3
-- title:
--   Theorem 1.3, p.4 — Swendsen–Wang dynamics mixes in $O(\log n)$ steps on almost every $\Delta$-regular graph throughout uniqueness
-- statement:
--   Fix integers $\Delta\ge3$ and $q\ge2$, and let $0<\beta<\beta_u(q,\mathbb T_\Delta)$, the tree uniqueness threshold. There is a constant $C>0$ such that, with probability $1-o(1)$, a uniformly random $\Delta$-regular graph $G$ on $n$ vertices is such that the Swendsen–Wang dynamics $P_{\mathrm{SW}}$ at parameters $q$ and $\beta$ on $G$ satisfies
--   $$t_{\mathrm{mix}}(P_{\mathrm{SW}})\le C\log n,\qquad t_{\mathrm{mix}}=\min\Bigl\{t\ge0:\max_{\sigma}\|P_{\mathrm{SW}}^t(\sigma,\cdot)-\mu_{G,\beta,q}\|_{\mathrm{TV}}\le\tfrac14\Bigr\},$$
--   where $\mu_{G,\beta,q}$ is the Potts law, the stationary law of the chain, and $\log$ is the natural logarithm.
--
--   The bound $O(\log n)$ is optimal and improves the previous $O(n^2\log n)$ bound for this chain. Above $\beta_u$ the chain is known to be exponentially slow in a metastability window for $q\ge3$, so the threshold is sharp.
--
--   **Formalization Note** The chain is the supplement's `swKernel`; the ensemble and the high-probability predicate are the mission's published `WithHighProb`, and $\beta_u(q,\mathbb T_\Delta)$ is the published `betaU`, exactly as in the mission's goal theorem.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: the constant of O(log n) inside a "with probability 1 − o(1)" statement → C is quantified before n and the graph event; reason: the stronger reading, and what the proof gives (§6, p.37): every constant is fixed first, then G is taken in the event
--   - encoding: mixing time O(log n) → d(⌊C log n⌋) ≤ 1/4 with d = distStationary of the Swendsen–Wang kernel against the Potts law; reason: d(t) is nonincreasing, so this says t_mix ≤ ⌊C log n⌋; it avoids the junk value of a natural-number sInf (paper.md R3)
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Theorem 1.3, p.4 (chain defined on p.3; proved in §6, pp.37–38)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_PottsLaw
import Definitions.Def_PottsRapidMixing_Supplement_SwendsenWang

open scoped Classical
open Filter Topology

namespace PottsRapidMixing.Supplement

/-- **Theorem 1.3** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.4). Fix integers `Δ ≥ 3`,
`q ≥ 2` and `0 < β < β_u(q, T_Δ)`. With probability `1 − o(1)`, a uniformly random Δ-regular graph `G`
on `n` vertices is such that the mixing time of the Swendsen–Wang dynamics at parameters `q` and `β` on
`G` is `O(log n)`.

**Formalization Note.** The `O`-constant `C` is fixed before `n` and outside the high-probability event,
as in `theorem_1_1`. `t_mix ≤ T` is stated as `d(⌊T⌋) ≤ 1/4` with `d = distStationary` of the chain
against the Potts law, its stationary law; `log` is the natural logarithm of the number of vertices. -/
theorem theorem_1_3 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβu : β < betaU (q : ℝ) Δ) :
    ∃ C : ℝ, 0 < C ∧ WithHighProb Δ (fun n G =>
      MarkovMixing.distStationary (swKernel G β q) (pottsLaw G β q)
        ⌊C * Real.log (n : ℝ)⌋₊ ≤ 1 / 4) := by sorry

end PottsRapidMixing.Supplement
