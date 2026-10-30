-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_3_3_1_a
-- name    : RamanujanLostNotebook.PartI.entry_3_3_1_a
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:19:05.567301+00:00
-- url     : https://prove2.me/theorems/90a8f1ff-9053-4987-b3ac-9ca0db340544
-- title:
--   Cubic continued fraction product
-- statement:
--   (a;q)_∞=∏_{k≥0}(1-a q^k); ch03Cubic(r) is the continued-fraction limit r/(1+(r³+r⁶)/(1+(r⁶+r¹²)/(1+…))). For parameters (r : ℂ) (hr : ‖r‖ < 1). Then ch03Cubic r = r * qPochInf (r ^ 3) (r ^ 6) / qPochInf (r ^ 9) (r ^ 18) ^ 3. The conclusion also asserts all displayed denominator nonvanishing and the required series, products and continued fractions converge. Differs from the printed source: We write q=r^3 and q^(1/3)=r, preserving the coherent branch in the printed product. Convergence of the continued fraction is asserted.
--
--   **Discrepancy from the printed source.** Differs from the printed source: We write q=r^3 and q^(1/3)=r, preserving the coherent branch in the printed product. Convergence of the continued fraction is asserted.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 3, Entry 3.3.1, p. 94.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Continuants
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Convergent
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Cubic
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03CubicConverges
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03SequenceValue
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf

namespace RamanujanLostNotebook.PartI
theorem entry_3_3_1_a (r : ℂ) (hr : ‖r‖ < 1) :
    (ch03CubicConverges r) ∧
    ((((qPochInf (r ^ 9)) (r ^ 18)) ^ 3) ≠ 0) ∧
    (Multipliable (fun k : ℕ => 1 - (r ^ 3) * (r ^ 6) ^ k)) ∧
    (Multipliable (fun k : ℕ => 1 - (r ^ 9) * (r ^ 18) ^ k)) ∧
    (ch03Cubic r = r * qPochInf (r ^ 3) (r ^ 6) / qPochInf (r ^ 9) (r ^ 18) ^ 3) := by sorry
end RamanujanLostNotebook.PartI
