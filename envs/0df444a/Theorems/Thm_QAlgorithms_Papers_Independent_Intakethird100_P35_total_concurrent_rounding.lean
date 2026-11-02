-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P35_total_concurrent_rounding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P35.total_concurrent_rounding
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:20:10.946076+00:00
-- url     : https://prove2.me/theorems/7656805f-a681-44b0-8e52-84b0eb8af856
-- title:
--   Lemma 3, Eq.(121): total concurrent rounding
-- statement:
--   Let $G'=(V,E')$ be finite and undirected, with $r\ge1$ indexed pairs $(s_i,t_i)$, distinct within each pair. Fix positive integers $m,k$ and finite nonnegative capacities $c_e$, allowing dependence on $m,k$. Let $N_i$ count all simple directed paths for pair $i$ and put $N=\sum_iN_i$. Let $f_{\mathrm{total}}^{\max}(c)$ maximize the sum of net source flows under conservation, nonnegativity, and one shared physical edge budget across all commodities and both orientations. In the multigraph having $\lfloor mkNc_e\rfloor$ labelled copies of each edge $e$, there is one concurrently edge-disjoint packing with $F_i$ paths for each pair such that
--
--   $$\sum_{i=1}^r F_i\ge mkN\left(f_{\mathrm{total}}^{\max}(c)-\frac1k\right).$$
--
--   The estimate rounds the total throughput objective. The sum defining $N$ differs from the maximum in Lemma 2; if every path set is empty, the empty packing applies.
-- source:
--   Linear programs for entanglement and key distribution in the quantum internet, arXiv:1809.03120v3, PDF p. 27, Lemma 3, Eq.(121): total concurrent rounding

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P35

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P35

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.27--28, Lemma 3, (121): concurrent total rounding, N=sum_i N_i.
Printed proof (128) says worst; the statement (121), objective (122), and estimate
(127) all say total. We state the lemma's total objective without using (128). -/
theorem total_concurrent_rounding {n e r : ℕ} (G : EdgeGraph n (Fin e))
    (hSimple : IsSimple G) (hr : 0 < r) (s t : Fin r → Fin n)
    (hst : ∀ i, s i ≠ t i) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (c : Fin e → ℝ) (hc : ∀ a, 0 ≤ c a) :
    ∃ P : Packing G (roundedCopies c m k (sumPathCount G s t)) s t,
      ((m * k * sumPathCount G s t : ℕ) : ℝ) *
        (totalValue G c s t - 1 / (k : ℝ)) ≤ ∑ i, (P.count i : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P35

end
