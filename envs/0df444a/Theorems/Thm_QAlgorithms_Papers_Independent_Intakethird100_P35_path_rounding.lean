-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P35_path_rounding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P35.path_rounding
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:19:03.028356+00:00
-- url     : https://prove2.me/theorems/dd575f4f-5cb6-4c41-a1ae-99300ca4f3d1
-- title:
--   Lemma 1, Eq.(57): path rounding
-- statement:
--   Let $G'=(V,E')$ be a finite undirected graph with distinct vertices $s,t$. Fix positive integers $m,k$ and finite nonnegative edge capacities $c_e$, which may depend on $m,k$. Let $N$ be the number of all simple directed paths from $s$ to $t$ in $G'$, and let $f_{s\to t}^{\max}(c)$ be the maximum net source outflow subject to nonnegative oriented flows, the shared constraint $f_{vw}+f_{wv}\le c_{\{v,w\}}$, and conservation at other vertices. Replace edge $e$ by $\lfloor mkNc_e\rfloor$ unit edges. There is a family of $F$ edge-disjoint $s$--$t$ paths in this actual multigraph satisfying
--
--   $$F\ge mkN\left(f_{s\to t}^{\max}(c)-\frac1k\right).$$
--
--   This turns fractional single-pair flow into an integral path packing. If no path exists, $N=0$ and the empty family satisfies the statement.
-- source:
--   Linear programs for entanglement and key distribution in the quantum internet, arXiv:1809.03120v3, PDF p. 20, Lemma 1, Eq.(57): path rounding

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P35

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P35

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.20, Lemma 1, (57): actual edge-disjoint paths in floor(mkNc).
The source's positive integers m,k are explicit; N is the number of ALL simple
s-to-t paths. Capacities are quantified after m,k and may depend on them. -/
theorem path_rounding {n e : ℕ} (G : EdgeGraph n (Fin e))
    (hSimple : IsSimple G) (s t : Fin n) (hst : s ≠ t)
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (c : Fin e → ℝ) (hc : ∀ a, 0 ≤ c a) :
    ∃ P : Packing G (roundedCopies c m k (pathCount G s t))
      (fun _ : Fin 1 => s) (fun _ : Fin 1 => t),
      ((m * k * pathCount G s t : ℕ) : ℝ) *
        (singlePairFlowValue G c s t - 1 / (k : ℝ)) ≤ (P.count 0 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P35

end
