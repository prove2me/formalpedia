-- Prove2me | Theorems.Thm_TSPSDPGap_theorem_4_1
-- name    : TSPSDPGap.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:51.782954+00:00
-- url     : https://prove2.me/theorems/5a2a39f5-3748-4d65-9c21-9bedbd486f2a
-- title:
--   Theorem 4.1 — the integrality gap of the de Klerk–Sotirov SDP is at least $z$ for every $z\in\mathbb N$
-- statement:
--   Let $z\in\mathbb N$. Then the integrality gap of SDP (2) is at least $z$:
--   $$
--   \sup_{D}\ \frac{\mathrm{OPT}_{\mathrm{TSP}}(D)}{\mathrm{OPT}_{\mathrm{SDP}}(D)}\ \ge\ z,
--   $$
--   the supremum taken over all metric and symmetric TSP instances $D$ (on $n+1\ge3$ cities), whatever indices $r,s\in[n+1]$ the relaxation SDP (2) fixes for each number of cities.
--
--   Consequently the integrality gap of the de Klerk–Sotirov SDP is unbounded (Corollary 4.2): no constant-factor approximation guarantee for the metric TSP can be certified by this relaxation.
--
--   **Formalization Note** Values lie in $[0,\infty]$, with $\mathrm{OPT}_{\mathrm{SDP}}$ an infimum over the feasible set. The indices $r(n),s(n)$ are arbitrary functions of the number of cities; the paper's proof takes $r=s=1$.
--
--   Differences from the source:
--   - generalization: SDP (2) with some indices s, r ∈ [n + 1] (the proof takes s = r = 1) → every rule r, s : (n : ℕ) → Fin (n + 1); reason: the paper leaves r, s arbitrary in the definition of SDP (2); the bound for every rule specializes to r = s = 1
--   - generalization: sup over all metric symmetric TSP instances → sup over instances on n + 1 ≥ 3 cities; reason: a lower bound on the supremum over fewer instances is a lower bound on the supremum over all instances
--   - reading: c̄ = vec(C₁[α, {r}] D[{s}, β]) → C₁ = C₁^(n+1) (inside sdp2Objective); reason: α ⊆ [n + 1], so only C₁^(n+1)[α, {r}] is defined
--   - encoding: OPT_TSP / OPT_SDP in ℝ, metric and symmetric costs → ℝ≥0∞ ratio of ENNReal.ofReal (MetricTSP.tspOpt D) and the ⨅ of ENNReal.ofReal (objective) over IsSDP1Feasible; MetricTSP.IsMetricCost; reason: Lean convention; on metric instances the objective is nonnegative and the feasible set nonempty (Solutions/verification/TSPSDPGap_lift.lean), so the values are the paper's
--   - encoding: 1-based indices → 0-based Fin n indices; reason: Lean convention; same instances
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Theorem 4.1, p.14 (restated and proved pp.27–28)

import Mathlib
import Definitions.Def_TSPSDPGap_integralityGapSDP2
open scoped ENNReal

namespace TSPSDPGap

/-- **Theorem 4.1: the integrality gap of SDP (2) is at least `z`, for every `z ∈ ℕ`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Theorem 4.1, p.14 (restated and proved pp.27–28):
"Let z ∈ ℕ. Then the integrality gap of SDP (2) is at least z."

For every rule choosing the indices `r(n), s(n) ∈ [n + 1]` of the de Klerk–Sotirov SDP (2) on
`n + 1` vertices, and every natural number `z`, the supremum of `OPT_TSP(D) / OPT_SDP(D)` over
all metric instances `D` is at least `z`.

**Formalization Note.** The gap is `integralityGapSDP2 r s` (values in `ℝ≥0∞`, supremum over
`n ≥ 2`, i.e. at least `3` cities). The indices `r, s` of SDP (2) are arbitrary functions of the
number of vertices; the paper's proof takes `r = s = 1` (`0` here, 0-based). -/
theorem theorem_4_1 (r s : (n : ℕ) → Fin (n + 1)) (z : ℕ) :
    (z : ℝ≥0∞) ≤ integralityGapSDP2 r s := by sorry

end TSPSDPGap
