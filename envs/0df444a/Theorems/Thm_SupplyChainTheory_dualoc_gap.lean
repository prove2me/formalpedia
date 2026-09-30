-- Prove2me | Theorems.Thm_SupplyChainTheory_dualoc_gap
-- name    : SupplyChainTheory.dualoc_gap
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:40:02.14224+00:00
-- url     : https://prove2.me/theorems/d4b9dd03-3bc8-4db9-b066-bef9cbaf5408
-- title:
--   Lemma 8.4: the DUALOC duality gap is $\sum_i \sum_{j \in J^+, j \ne j^+(i)} \max\{0, v^+_i - \hat c_{ij}\}$
-- statement:
--   **Lemma 8.4.** Let $v^+$ and $J^+$ satisfy PDP1 and PDP2, let $j^+(i)$ be a nearest facility
--   of $J^+$ to each customer $i$, and let $(x^+, y^+)$ be the primal solution (8.52)-(8.53). Then
--   the objective value $z^+_P = \sum_{j \in J^+} f_j + \sum_i \hat c_{i, j^+(i)}$ of (UFLP-P) under
--   $(x^+, y^+)$ and the objective value $z^+_D = \sum_i v^+_i$ of the condensed dual (UFLP-CD)
--   under $v^+$ satisfy
--
--   $$ z^+_P - z^+_D \;=\; \sum_{i \in I}\ \sum_{j \in J^+,\ j \ne j^+(i)} \max\{0, v^+_i - \hat c_{ij}\}. $$
--
--   The book omits the proof (Problem 8.40). By PDP1 each fixed cost $f_j$, $j \in J^+$, is the
--   sum of the dual slacks $\max\{0, v_i - \hat c_{ij}\}$, and by PDP2 the slack of $j^+(i)$ is
--   exactly $v_i - \hat c_{i,j^+(i)}$; the remaining slacks are the gap. This is what the
--   dual-adjustment procedure attacks.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 284, Sect. 8.2.4.1, Lemma 8.4: 'Proof. Omitted; see Problem 8.40'

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem dualoc_gap {n m : ℕ} (chat : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (v : Fin n → ℝ)
    (Jp : Finset (Fin m)) (a : Fin n → Fin m) (hPDP : PDP chat f v Jp) (ha : NearestIn chat Jp a) :
    (∑ j ∈ Jp, f j + ∑ i, chat i (a i)) - ∑ i, v i
      = ∑ i, ∑ j ∈ Jp.erase (a i), max 0 (v i - chat i j) := by sorry

end SupplyChainTheory
