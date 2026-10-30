-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_18_2_6
-- name    : RamanujanLostNotebook.PartI.entry_18_2_6
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:37:46.61834+00:00
-- url     : https://prove2.me/theorems/30da9fe9-53d8-4a9d-a381-19a89db428a4
-- title:
--   Six-triangle Lambert series
-- statement:
--   For every complex r with |r|<1, the displayed series converge absolutely, all displayed denominators are nonzero, and r³ψ(r⁴)^6 = (1/16)∑_{n≥0}(2n+1)²r^(2n+1)/(1+r^(4n+2))-(1/16)∑_{n≥0}(-1)^n(2n+1)²r^(2n+1)/(1-r^(4n+2)). Here φ(z)=∑_{j∈ℤ}z^(j²), ψ(z)=∑_{j≥0}z^(j(j+1)/2), f(-z)=∏_{j≥1}(1-z^j), a(z)=∑_{j,k∈ℤ}z^(j²+jk+k²), T(z)=∑_{j,k∈ℤ}z^(j²+jk+2k²), (n/p) is the Legendre symbol and χ₀,p is the principal character modulo p. Differs from the printed source: we write the source q as r² and q^(1/2) as r, for every complex |r|<1, turning all half powers on p.398 into natural powers. This is our branch-explicit interpretation. Both sides are odd in r, so the two square-root choices give equivalent identities; r=0 is included. Numerical evidence at four points and 40 coefficients is not a proof.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we write the source q as r² and q^(1/2) as r, for every complex |r|<1, turning all half powers on p.398 into natural powers. This is our branch-explicit interpretation. Both sides are odd in r, so the two square-root choices give equivalent identities; r=0 is included. Numerical evidence at four points and 40 coefficients is not a proof.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 18, Entry 18.2.6, p. 398, eq. (3.23).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_thetaPsi

namespace RamanujanLostNotebook.PartI
theorem entry_18_2_6 (r : ℂ) (hr : ‖r‖ < 1) :
    let s1 : ℕ → ℂ := fun n => ((2 * n + 1 : ℕ) : ℂ) ^ 2 * r ^ (2 * n + 1) / (1 + r ^ (4 * n + 2))
    let s2 : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * ((2 * n + 1 : ℕ) : ℂ) ^ 2 * r ^ (2 * n + 1) / (1 - r ^ (4 * n + 2))
    Summable s1 ∧
      Summable s2 ∧
      (∀ n : ℕ, (1 + r ^ (4 * n + 2)) ≠ 0) ∧
      (∀ n : ℕ, (1 - r ^ (4 * n + 2)) ≠ 0) ∧
      r ^ 3 * thetaPsi (r ^ 4) ^ 6 = (1 / 16 : ℂ) * (∑' n : ℕ, s1 n) - (1 / 16 : ℂ) * (∑' n : ℕ, s2 n) := by sorry
end RamanujanLostNotebook.PartI
