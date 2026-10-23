-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_5_2_1
-- name    : RamanujanLostNotebook.PartI.entry_5_2_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T07:02:38.190423+00:00
-- url     : https://prove2.me/theorems/ff93971a-d769-4f02-820f-36fde77b6599
-- title:
--   Small-parameter fraction at primitive roots
-- statement:
--   Differs from the printed source: The manuscript formula (5.1.6), p.126, has no range for a. We use the book’s own restriction |a|<1/4 in Entry 5.2.1, p.131, and explicitly conclude convergence and nonvanishing.
--   For b₀+K(c_j/b_j), canonical continuants have P_-1=1,P_0=b₀,Q_-1=0,Q_0=1 and P_n=b_n P_(n-1)+c_n P_(n-2), Q_n=b_n Q_(n-1)+c_n Q_(n-2), n≥1. Indices start at 1. For a primitive mth root q, m≥1, and complex |a|<1/4, all canonical denominators are nonzero and the approximants of a/(1+aq/(1+...)) converge to (Pₘ₋₁(a)+(−1+sqrt(1+4aᵐ))/2)/Qₘ₋₁(a). The square root is the branch equal to 1 at a=0, here the principal complex square root.
--
--   **Discrepancy from the printed source.** The manuscript formula (5.1.6), p.126, has no range for a. We use the book’s own restriction |a|<1/4 in Entry 5.2.1, p.131, and explicitly conclude convergence and nonvanishing.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 5, Entry 5.2.1, p. 131, eq. (5.2.12).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05Continuants
import Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05P
import Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05Q
open Filter Topology

namespace RamanujanLostNotebook.PartI
theorem entry_5_2_1 (m : ℕ) (hm : 0 < m) (a q : ℂ)
    (hq : IsPrimitiveRoot q m) (ha : ‖a‖ < (1 / 4 : ℝ)) :
    (∀ N : ℕ, ch05Q 0 (fun k => a * q ^ (k - 1)) (fun _ => 1) N ≠ 0) ∧
    Tendsto (fun N : ℕ =>
      ch05P 0 (fun k => a * q ^ (k - 1)) (fun _ => 1) N /
        ch05Q 0 (fun k => a * q ^ (k - 1)) (fun _ => 1) N) atTop
      (𝓝 ((ch05P 0 (fun k => a * q ^ (k - 1)) (fun _ => 1) (m - 1) +
        (-1 + (1 + 4 * a ^ m) ^ (1 / 2 : ℂ)) / 2) /
        ch05Q 0 (fun k => a * q ^ (k - 1)) (fun _ => 1) (m - 1))) := by sorry
end RamanujanLostNotebook.PartI
