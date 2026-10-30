-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_13_6_1_product
-- name    : RamanujanLostNotebook.PartI.entry_13_6_1_product
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:46:30.525172+00:00
-- url     : https://prove2.me/theorems/b9026677-5a3f-4e08-9ca4-d14754ff6541
-- title:
--   Ramanujan product with recursive denominators
-- statement:
--   For 0<q<1/4 and every complex a, all recursive denominators converge and are nonzero, and the entire Rogers–Ramanujan type series equals the convergent product of 1+a q^(2N-1)/omega_N.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13, Entry 13.6.1, p. 297, eq. (13.1.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Falling
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Omega
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Partitions
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Rec
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13ThetaScaled
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Y
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13YVec
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch

namespace RamanujanLostNotebook.PartI
theorem entry_13_6_1_product (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1 / 4) (a : ℂ) :
    (∀ N : ℕ, 0 < N →
      Summable (fun i : ℕ => ch13Y (q : ℂ) (i + 1) * (q : ℂ) ^ (N * (i + 1))) ∧
      ch13Omega (q : ℂ) N ≠ 0) ∧
    Multipliable (fun n : ℕ => 1 + a * (q : ℂ) ^ (2 * n + 1) / ch13Omega (q : ℂ) (n + 1)) ∧
    HasSum (fun n : ℕ => a ^ n * (q : ℂ) ^ (n * n) / qPoch (q : ℂ) (q : ℂ) n)
      (∏' n : ℕ, (1 + a * (q : ℂ) ^ (2 * n + 1) / ch13Omega (q : ℂ) (n + 1))) := by sorry
end RamanujanLostNotebook.PartI
