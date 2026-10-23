-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIII_entry_9_1_1_a
-- name    : RamanujanLostNotebook.PartIII.entry_9_1_1_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T08:05:37.063978+00:00
-- url     : https://prove2.me/theorems/b861236d-f816-4253-b0f6-0bee6c3db17c
-- title:
--   Circular factorization for every positive order
-- statement:
--   Differs from the printed source: Our interpretation: use the explicit uniformizer t, so ch09Factor n t is the printed F_n(t²). This keeps both square-root sheets instead of assigning an unspecified fractional power of the product; the lattice exponent in (9.2.12), p.341, is the t-exponent. The source mixes the arguments in (9.2.3) and (9.2.12); the initial term in (9.1.2) fixes the normalization. Fractional powers use each base’s principal cpow and the compatible product of its square roots. The allowed complete residue system is 0,...,n−1 as in the book’s (9.1.3).
--   For every positive integer n and complex a,b with |ab|<1, the n residue-class series and f(a,b) converge absolutely, the defining lattice series has sum F_n(ab) on the compatible sheet, and the sum of their nth powers is f(a,b)F_n(ab). All powers in each residue series use the individual principal logarithms of a,b; its factor has uniformizer a^(1/2)b^(1/2). Zero a or b is allowed. Residues are 0,...,n−1, the complete residue system used in (9.1.3).
--
--   **Discrepancy from the printed source.** Our interpretation: use the explicit uniformizer t, so ch09Factor n t is the printed F_n(t²). This keeps both square-root sheets instead of assigning an unspecified fractional power of the product; the lattice exponent in (9.2.12), p.341, is the t-exponent. The source mixes the arguments in (9.2.3) and (9.2.12); the initial term in (9.1.2) fixes the normalization. Fractional powers use each base’s principal cpow and the compatible product of its square roots. The allowed complete residue system is 0,...,n−1 as in the book’s (9.1.3).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 9, Entry 9.1.1, p. 337, eq. (9.1.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch09_ch09FTerm
import Definitions.Def_RamanujanLostNotebook_PartIII_ch09_ch09Factor
import Definitions.Def_RamanujanLostNotebook_PartIII_ch09_ch09ResidueTerm
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_ramanujanTheta

namespace RamanujanLostNotebook.PartIII
theorem entry_9_1_1_a (n : ℕ) (hn : 0 < n) (a b : ℂ) (hab : ‖a * b‖ < 1) :
    (∀ r ∈ Finset.range n, Summable (ch09ResidueTerm n r a b)) ∧
    Summable (fun k : ℤ => a ^ (k * (k + 1) / 2).toNat *
      b ^ (k * (k - 1) / 2).toNat) ∧
    HasSum (ch09FTerm n (a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ)))
      (ch09Factor n (a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ))) ∧
    (∑ r ∈ Finset.range n, (∑' k : ℤ, ch09ResidueTerm n r a b k) ^ n) =
      ramanujanTheta a b * ch09Factor n (a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ)) := by sorry
end RamanujanLostNotebook.PartIII
