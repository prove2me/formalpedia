-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_4_11
-- name    : SmoothedMIS.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:04.48483+00:00
-- url     : https://prove2.me/theorems/137bf266-01b7-45f3-8645-146b8e0e6058
-- title:
--   Lemma 4.11 — robust success implies domination
-- statement:
--   Fix any outcome of the random edges and marks, a base graph $G$, and parameters $\beta,a$. If $E$ holds, $h\in V_{hi}$, and some $v\in T_h$ is robustly successful, then $v\in S$; hence $h\notin\mathcal A$.
--
--   This deterministic step turns the probability bounds of Case (2b) into the conclusion $\mathcal A=\emptyset$ of Lemma 4.13.
--
--   Differences from the source:
--   - generalization: the setting of Case (2b) (M > 0, z_H < n/√B0, z_Q < n/√t, β = 2a, a ≥ 48(c+3)) → every n, every base graph, every reals β and a, every coin outcome; reason: the proof uses only E, h ∈ V_hi, v ∈ T_h and robust success; the paper's case is a special case
--   - encoding: the sets under the random edges and the marks → functions of a fixed coin outcome ω = (ω_R, ω_κ) of the analysis model; reason: the statement is pointwise
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 4.11, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SmoothedMIS_testSet

namespace SmoothedMIS

/-- **Lemma 4.11 (Robust success implies domination)** (Dey, Dufoulon, Moses Jr., Pandurangan,
*Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 4.11, p.26). If `E`
holds, `h ∈ V_hi`, and some `v ∈ T_h` is robustly successful, then `v ∈ S`; hence `h ∉ 𝒜`.

**Formalization Note** Pointwise in the coins `ω`, for every `n`, `β`, `a` (the test set `T_h`
depends on `a` through `t`) and every base graph; the case hypotheses of §4.2.1 are not needed. -/
theorem lemma_4_11 (n : ℕ) (β a : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) (h v : Fin n) :
    EventE β G ω.1 → h ∈ Vhi β G ω.1 → v ∈ testSet a G ω h → RobustSuccess G ω h v →
      v ∈ helpers β G ω ∧ h ∉ activeSet β G ω := by sorry

end SmoothedMIS
