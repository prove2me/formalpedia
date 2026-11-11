-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_32
-- name    : WeakStrongMSR.lemma_3_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:30:53.526782+00:00
-- url     : https://prove2.me/theorems/c54dd679-2b01-4b58-bb62-609a85145e99
-- title:
--   Lemma 3.32 — MSR on any subset $S$ with centres in $S$ costs at most $2\,\mathrm{OPT}$
-- statement:
--   Let $d$ be a metric on $X$ and $k\ge1$. For every subset $S\subseteq X$, the optimum minimum-sum-of-radii cost of $S$ with at most $k$ clusters, on the metric induced by $S$ and with centres restricted to $S$, satisfies
--   $$\mathrm{opt}_S\le 2\,\mathrm{OPT}.$$
--
--   It bounds the cost of compression, which runs an offline approximation on the strong set only.
--
--   Differences from the source:
--   - encoding: "the metric induced by S, with centres restricted to S" → opt_S over labellings σ of all points, clusters σ⁻¹(j) ∩ S, centres in S; 0 for S = ∅; reason: same value; empty clusters cost 0
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.32, p.26 (PDF 27)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Compress

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.32** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.26, PDF p.27).
"For every subset S ⊆ X, the optimum minimum-sum-of-radii cost on the metric induced by S, with
centres restricted to S, is at most 2 OPT."

For a metric `d`, `k ≥ 1` and every set `S` of points, `optOn d k S ≤ 2 · OPT`, where `optOn` is the
MSR optimum of `S` with at most `k` clusters and centres in `S`, and `OPT = msrOpt d k`. -/
theorem lemma_3_32 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d) (k : ℕ)
    (hk : 1 ≤ k) (S : Finset (Fin n)) :
    optOn d k S ≤ 2 * MinSumRadiiPTAS.Main.msrOpt d k := by sorry

end WeakStrongMSR
