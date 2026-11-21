-- Prove2me | Theorems.Thm_RiemannMasullo_lattice_radial_weight_monomial_domination
-- name    : RiemannMasullo.lattice_radial_weight_monomial_domination
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:16:08.493426+00:00
-- url     : https://prove2.me/theorems/94de600d-2a0a-4dab-9422-b2bea5de67a4
-- title:
--   A single support-dependent lattice monomial dominates the weighted summability denominator
-- statement:
--   On an integer lattice of rank r, (1+‖a‖)^j times the product of 1+a_i² is bounded by (r+2)^j 2^r times the product of |a_i|^(j+2) over its nonzero coordinates.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606

import Mathlib

namespace RiemannMasullo
theorem lattice_radial_weight_monomial_domination (r j : ℕ) (a : Fin r → ℤ) :
    let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i => (a i:ℝ))
    (1+‖v‖)^j * (∏ i, (1+(a i:ℝ)^2)) ≤
      (((r:ℝ)+2)^j * 2^r) * ∏ i, |(a i:ℝ)|^(if a i=0 then 0 else j+2) := by sorry
end RiemannMasullo
