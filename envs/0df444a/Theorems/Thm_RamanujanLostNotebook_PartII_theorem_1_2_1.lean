-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_theorem_1_2_1
-- name    : RamanujanLostNotebook.PartII.theorem_1_2_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T11:49:18.339136+00:00
-- url     : https://prove2.me/theorems/98914e1f-03e5-42f1-bd9c-9e6fae613cdf
-- title:
--   Heine transformation with positive step
-- statement:
--   Differs from the printed source: b ≠ 0 is explicit because c/b occurs; c q^j ≠ 1 and at(q^h)^j ≠ 1 for every j exclude poles of (c;q) and (at;q^h). The bound ‖q‖ < 1 restates the chapter convention. For complex a,b,c,t,q and positive natural h, ‖q‖<1, ‖t‖<1, ‖b‖<1, b≠0, cq^j≠1 and at(q^h)^j≠1 for every j≥0: For h>0, sum_m (a;q^h)_m(b;q)_{hm}t^m/((q^h;q^h)_m(c;q)_{hm}) = (b;q)_∞(at;q^h)_∞/((c;q)_∞(t;q^h)_∞) times sum_m (c/b;q)_m(t;q^h)_m b^m/((q;q)_m(at;q^h)_m); both sums converge.
--
--   **Discrepancy from the printed source.** Differs from the printed source: b ≠ 0 is explicit because c/b occurs; c q^j ≠ 1 and at(q^h)^j ≠ 1 for every j exclude poles of (c;q) and (at;q^h). The bound ‖q‖ < 1 restates the chapter convention.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 1, Theorem 1.2.1, p. 6, eq. (1.2.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

namespace RamanujanLostNotebook.PartII
theorem theorem_1_2_1 (a b c t q : ℂ) (h : ℕ) (hh : 0 < h)
    (hq : ‖q‖ < 1) (ht : ‖t‖ < 1) (hb : ‖b‖ < 1) (hb0 : b ≠ 0)
    (hc : ∀ j : ℕ, c * q ^ j ≠ 1)
    (hat : ∀ j : ℕ, a * t * (q ^ h) ^ j ≠ 1) :
    Summable (fun m : ℕ => qPoch a (q ^ h) m * qPoch b q (h * m) * t ^ m /
      (qPoch (q ^ h) (q ^ h) m * qPoch c q (h * m))) ∧
    Summable (fun m : ℕ => qPoch (c / b) q m * qPoch t (q ^ h) m * b ^ m /
      (qPoch q q m * qPoch (a * t) (q ^ h) m)) ∧
    (∑' m : ℕ, qPoch a (q ^ h) m * qPoch b q (h * m) * t ^ m /
      (qPoch (q ^ h) (q ^ h) m * qPoch c q (h * m))) =
      qPochInf b q * qPochInf (a * t) (q ^ h) /
        (qPochInf c q * qPochInf t (q ^ h)) *
        (∑' m : ℕ, qPoch (c / b) q m * qPoch t (q ^ h) m * b ^ m /
          (qPoch q q m * qPoch (a * t) (q ^ h) m)) := by sorry
end RamanujanLostNotebook.PartII
