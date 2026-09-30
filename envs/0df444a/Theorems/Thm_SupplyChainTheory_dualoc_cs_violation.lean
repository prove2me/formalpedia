-- Prove2me | Theorems.Thm_SupplyChainTheory_dualoc_cs_violation
-- name    : SupplyChainTheory.dualoc_cs_violation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:40:53.125859+00:00
-- url     : https://prove2.me/theorems/8e55577a-6a94-4529-8e79-15067d6b89e9
-- title:
--   Lemma 8.6: customer $i$ violates complementary slackness iff $v_i > \hat c_{ij}$ for at least two $j \in J^+$
-- statement:
--   **Lemma 8.6.** Let $v$ and $J^+$ satisfy PDP1 and PDP2, let $j^+(i)$ be a nearest facility of
--   $J^+$ to each customer, and let $(x^+, y^+)$ be the primal solution (8.52)-(8.53). Then
--   customer $i$ violates the complementary slackness condition (8.51),
--   $\max\{0, v_i - \hat c_{ij}\}(y^+_{ij} - x^+_j) = 0$ for all $j$, if and only if $v_i > \hat c_{ij}$
--   for at least two $j \in J^+$.
--
--   A violation is a facility $j' \in J^+$ other than $j^+(i)$ with $v_i > \hat c_{ij'}$; since
--   $\hat c_{i,j^+(i)} \le \hat c_{ij'}$, the nearest facility is then a second one. This identifies
--   the dual variables that the dual-adjustment procedure of DUALOC reduces.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 289, Sect. 8.2.4.3, Lemma 8.6 and its proof

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem dualoc_cs_violation {n m : ℕ} (chat : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (v : Fin n → ℝ)
    (Jp : Finset (Fin m)) (a : Fin n → Fin m) (hPDP : PDP chat f v Jp) (ha : NearestIn chat Jp a)
    (i : Fin n) :
    ViolatesCS chat v Jp a i ↔ 2 ≤ (Jp.filter (fun j => chat i j < v i)).card := by sorry

end SupplyChainTheory
