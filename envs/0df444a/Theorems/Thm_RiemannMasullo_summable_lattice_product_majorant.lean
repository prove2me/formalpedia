-- Prove2me | Theorems.Thm_RiemannMasullo_summable_lattice_product_majorant
-- name    : RiemannMasullo.summable_lattice_product_majorant
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:11:49.970974+00:00
-- url     : https://prove2.me/theorems/953a1555-2565-46d0-8762-c93b71937496
-- title:
--   A separable summable majorant for the integer lattice, with its exact product mass
-- statement:
--   The product of (1+a_i²)^(-1) is summable over the rank-r integer lattice. Its total mass is the r-th power of the one-dimensional mass, including rank zero.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606

import Mathlib

namespace RiemannMasullo
theorem summable_lattice_product_majorant (r : ℕ) :
    let b := fun k : ℤ => 1/(1+(k:ℝ)^2)
    Summable (fun a : Fin r → ℤ => ∏ i, b (a i)) ∧
      (∑' a : Fin r → ℤ, ∏ i, b (a i)) = (∑' k : ℤ, b k)^r := by sorry
end RiemannMasullo
