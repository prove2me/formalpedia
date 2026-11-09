-- Prove2me | Theorems.Thm_WeldedPath_observation_3_3
-- name    : WeldedPath.observation_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:04:14.659105+00:00
-- url     : https://prove2.me/theorems/7da2f7cc-ab8e-4639-a894-786068e25219
-- title:
--   Observation 3.3 — every permuted edge class has at least $N_l/4$ edges
-- statement:
--   Let $n\ge 16$ be even, $l\in[2,n-4]$, and let $G_n$ be a valid welded trees instance. Then every permuted edge class $E_b$, $b\in B_{\mathrm{edge}}$, satisfies
--   $$
--   |E_b|\ \ge\ \frac{N_l}{4},\qquad N_l=2^{n-l}.
--   $$
--
--   This size bound is what lets the compressed-oracle estimates, which need $|E_b|$ large compared with the number of records, apply to every edge permutation.
--
--   Differences from the source:
--   - encoding: for every σ_b : E_b → E_b, |E_b| ≥ N_l/4 → |E_b| ≥ 2^{n−l}/4 for every b ∈ B_edge; reason: σ_b does not occur in the conclusion
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Observation 3.3, p.17

import Mathlib
import Definitions.Def_WeldedPath_bEdge

namespace WeldedPath

/-- **Observation 3.3** (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder,
arXiv:2611.05912 (sha256 b31400a0…), Observation 3.3, p.17). Assume that `n ≥ 16`. For every
`b ∈ B_edge` and every `σ_b : E_b → E_b`, `|E_b| ≥ N_l/4`, where `N_l = 2^{n−l}`.

**Formalization Note.** The standing assumptions of §3.1 (p.14), `n` even and `l ∈ [2, n − 4]`,
are hypotheses. The quantifier over `σ_b` does not occur in the conclusion and is omitted. -/
theorem observation_3_3 (n l : ℕ) (hn : Even n) (hn16 : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid) :
    ∀ b ∈ BEdge n l, (2 : ℝ) ^ (n - l) / 4 ≤ ((G.classEdges l b).card : ℝ) := by sorry

end WeldedPath
