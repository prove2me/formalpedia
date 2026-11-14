-- Prove2me | Theorems.Thm_StableMSR_Recovery_clustering_scale_selection
-- name    : StableMSR.Recovery.clustering_scale_selection
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T14:48:06.19789+00:00
-- url     : https://prove2.me/theorems/cbbbcab0-086c-496f-92dd-4f8cd2e40f68
-- title:
--   Lemma A.4: few large clusters or an enumerated dyadic scale
-- statement:
--   Let a finite metric space of $n$ points be partitioned into $k<n$ nonempty clusters, and let $0<\varepsilon<1$. Write $R$ for the largest cluster radius, $b=\varepsilon R/4$, $T$ for the clusters of radius at least $b$, $M=\sum_{C\in T}r(C)$, and $\rho=\varepsilon M/4$. With $\sigma=512$ and $N_\varepsilon=\lceil16\sigma/\varepsilon^2\rceil$, one of the following holds:
--
--   1. $\rho<\sigma R$ and $|T|\le N_\varepsilon$.
--   2. There is an integer $j$ with $9\le j\le\lceil\log_2 n\rceil$ such that, for $L=2^jR$,
--   $$\sigma R\le L\le\rho<2L,\qquad M/L<8/\varepsilon.$$
--
--   This is the deterministic scale-selection portion of Lemma A.4. It identifies either the bounded enumeration branch or a scale in Algorithm 1's finite list. The probabilistic partition guarantee is a separate obligation. The numerical argument needs feasibility and metricity, but no optimality or stability assumption.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Lemma A.4, first two assertions and their proof; Table 2 for the exact constants.

import Definitions.Def_StableMSR_Recovery_Geometry
import Definitions.Def_StableMSR_Recovery_Parameters

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem clustering_scale_selection {n k : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (O : Partition n) (hO : Feasible Finset.univ k O)
    (hkn : k < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (densityScale d O ε < sigma * largestRadius d O ∧
      (largeClusters d O ε).card ≤ fewBound ε) ∨
    (∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ ∧
      sigma * largestRadius d O ≤ (2 : ℝ) ^ j * largestRadius d O ∧
      (2 : ℝ) ^ j * largestRadius d O ≤ densityScale d O ε ∧
      densityScale d O ε < 2 * ((2 : ℝ) ^ j * largestRadius d O) ∧
      largeMass d O ε / ((2 : ℝ) ^ j * largestRadius d O) < 8 / ε) := by sorry

end StableMSR.Recovery
