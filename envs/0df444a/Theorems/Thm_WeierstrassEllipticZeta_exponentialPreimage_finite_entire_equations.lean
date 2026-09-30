-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exponentialPreimage_finite_entire_equations
-- name    : WeierstrassEllipticZeta.exponentialPreimage_finite_entire_equations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T03:17:33.603476+00:00
-- url     : https://prove2.me/theorems/f952c142-d9dd-4cfc-9d57-f95e5102ad44
-- title:
--   Every model has finite entire exponential preimage equations
-- statement:
--   For every compatible Model M and actual algebraic subgroup H, pull back all bihomogeneous equations vanishing on H under the explicit entire exponential coordinates. Their common zero locus in C³ is defined by finitely many entire functions, by the Hilbert basis theorem. This result does not assert that the inverse image is additive and does not use connectedness or a chosen canonical group model.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, exponential maps and Lemma A.1. Supporting application geometry belongs to Senthil, not Philippon.

import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.exponentialPreimage_finite_entire_equations
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (M : Model S) (H : AlgebraicSubgroup M.group) :
    ∃ F : Finset ((Fin 3 → ℂ) → ℂ),
      (∀ f ∈ F, AnalyticOnNhd ℂ f Set.univ) ∧
      ∀ v, v ∈ M.exponentialPreimage H ↔ ∀ f ∈ F, f v = 0 := by sorry
