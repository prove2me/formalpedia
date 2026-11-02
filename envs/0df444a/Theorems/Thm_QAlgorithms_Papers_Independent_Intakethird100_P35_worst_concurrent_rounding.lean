-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P35_worst_concurrent_rounding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P35.worst_concurrent_rounding
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:19:32.947316+00:00
-- url     : https://prove2.me/theorems/0817b9ec-3c09-406c-9f37-dd4f00d58fd0
-- title:
--   Lemma 2, Eq.(107): worst-case concurrent rounding
-- statement:
--   Let $G'=(V,E')$ be finite and undirected, with $r\ge1$ indexed terminal pairs $(s_i,t_i)$, distinct within each pair. Pairs may share vertices. Fix positive integers $m,k$ and finite capacities $c_e\ge0$, which may depend on them. Let $N_i$ count all simple directed $s_i$--$t_i$ paths, $N=\max_iN_i$, and let $f_{\mathrm{worst}}^{\max}(c)$ be the maximum common lower bound on the net source flows of a single concurrent flow family. All commodities and both directions share each physical capacity. In the multigraph with $\lfloor mkNc_e\rfloor$ labelled copies of edge $e$, a single packing gives every pair $F_i$ paths, with disjointness across all pairs as well as within each pair, and
--
--   $$\forall i,\qquad F_i\ge mkN\left(f_{\mathrm{worst}}^{\max}(c)-\frac1k\right).$$
--
--   This preserves concurrency when rounding the fair-flow objective. Empty path domains are allowed.
-- source:
--   Linear programs for entanglement and key distribution in the quantum internet, arXiv:1809.03120v3, PDF p. 26, Lemma 2, Eq.(107): worst-case concurrent rounding

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P35

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P35

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.26--27, Lemma 2, (107): concurrent worst-case rounding.
N=max_i N_i is computed, and every commodity shares one edge-copy packing. -/
theorem worst_concurrent_rounding {n e r : ℕ} (G : EdgeGraph n (Fin e))
    (hSimple : IsSimple G) (hr : 0 < r) (s t : Fin r → Fin n)
    (hst : ∀ i, s i ≠ t i) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (c : Fin e → ℝ) (hc : ∀ a, 0 ≤ c a) :
    ∃ P : Packing G (roundedCopies c m k (maxPathCount G s t)) s t,
      ∀ i, ((m * k * maxPathCount G s t : ℕ) : ℝ) *
        (worstValue G c s t - 1 / (k : ℝ)) ≤ (P.count i : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P35

end
