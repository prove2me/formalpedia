-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_entry_4_2_3
-- name    : RamanujanLostNotebook.PartII.entry_4_2_3
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T07:43:03.598998+00:00
-- url     : https://prove2.me/theorems/6d09965d-b64d-44bc-96e1-041a1b07ab7c
-- title:
--   Three-parameter Watson specialization
-- statement:
--   For all complex a, b, c, q with |q|<1, assuming ∀ k : ℕ, 1 + c * q ^ (k + 1) ≠ 0. Write qPoch(x,r,n)=∏_{k=0}^{n-1}(1-xr^k); qPochInf(x,r)=∏_{k≥0}(1-xr^k); ch04ScaledPoch(b,x,r,n)=∏_{k=0}^{n-1}(b-xr^k). Let L_n=ch04ScaledPoch b (-a * q) q n * q ^ (n * (n + 1) / 2) / (qPoch q q n * qPoch (-c * q) q n) and R_n=(-1 : ℂ) ^ n * qPoch (a * q) q n * ch04ScaledPoch b (-a * q) q n * ch04ScaledPoch c (-a * q) q n * (1 - a * q ^ (2 * n + 1)) * q ^ (n * (3 * n + 1) / 2) * qPochInf (-b * q ^ (n + 1)) q / (qPoch q q n * qPoch (-c * q) q n). The series ∑L_n converges absolutely and ∑R_n converges absolutely with sum qPochInf (a * q) q·∑L_n. Differs from the printed source: Our statement clears (-bq;q)_∞ using its shifted tails and replaces reciprocal-b and reciprocal-c blocks by finite polynomial products; b=0 and c=0 are retained. The genuine (-cq;q)_n poles are explicitly excluded.
--
--   **Discrepancy from the printed source.** Differs from the printed source: Our statement clears (-bq;q)_∞ using its shifted tails and replaces reciprocal-b and reciprocal-c blocks by finite polynomial products; b=0 and c=0 are retained. The genuine (-cq;q)_n poles are explicitly excluded.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 4, Entry 4.2.3, p. 84.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch04_ch04ScaledPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

namespace RamanujanLostNotebook.PartII
theorem entry_4_2_3 (a b c q : ℂ) (hq : ‖q‖ < 1)
    (hregular : ∀ k : ℕ, 1 + c * q ^ (k + 1) ≠ 0) :
    Summable (fun n : ℕ =>
      ch04ScaledPoch b (-a * q) q n * q ^ (n * (n + 1) / 2) / (qPoch q q n * qPoch (-c * q) q n)) ∧
    HasSum (fun n : ℕ =>
      (-1 : ℂ) ^ n * qPoch (a * q) q n * ch04ScaledPoch b (-a * q) q n * ch04ScaledPoch c (-a * q) q n * (1 - a * q ^ (2 * n + 1)) * q ^ (n * (3 * n + 1) / 2) * qPochInf (-b * q ^ (n + 1)) q / (qPoch q q n * qPoch (-c * q) q n))
      ((qPochInf (a * q) q) * (∑' n : ℕ,
        ch04ScaledPoch b (-a * q) q n * q ^ (n * (n + 1) / 2) / (qPoch q q n * qPoch (-c * q) q n))) := by sorry
end RamanujanLostNotebook.PartII
