-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ArtinSchreier_frobeniusCombo_ne
-- name    : QEC.Coding.AlgebraicGeometry.ArtinSchreier.frobeniusCombo_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:56.66851+00:00
-- url     : https://prove2.me/theorems/37d6adb3-8731-444c-a4fe-4d0a65e05983
-- title:
--   Artin Schreier: frobenius Combo ne
-- statement:
--   **Frobenius-combination exclusion.** `u` is never of the form
--   `∑ cⱼ a^{2^j}` with top coefficient `c_m = 1` and all coefficients
--   Frobenius-fixed (`cⱼ³² = cⱼ`, hence `ν cⱼ ∈ {0, 1}`) for `1 ≤ m ≤ 4`.
--   Writing `ν a = exp r`: the terms have valuations `exp (2^j·r)` (up to the
--   coefficient factor `ν cⱼ ∈ {0, 1}`), and the strict maximum is attained at
--   a unique `j₀` (`j₀ = m` when `r > 0`, the least nonzero-coefficient index when
--   `r < 0`), so `ν u = exp (2^{j₀}·r)`. Equating with `exp 33` forces
--   `r = 33/2^{j₀}`; for `r < 0` this is positive, and for `r > 0` it is not an
--   integer while `r : ℤ` — both impossible. The `r = 0` case has all valuations
--   `≤ 1 < exp 33`. This excludes the surviving case of the Frobenius-iteration
--   argument for the irreducibility of `X³² + X - C u`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L172-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L172-L355

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]

theorem QEC.Coding.AlgebraicGeometry.ArtinSchreier.frobeniusCombo_ne (ν : Valuation F ℤᵐ⁰) (u : F)
    (hu : ν u = WithZero.exp (33 : ℤ)) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (a : F) (c : Fin (m + 1) → F) (hc : ∀ j : Fin (m + 1), c j ^ 32 = c j)
    (hcTop : c ⟨m, Nat.lt_succ_self m⟩ = 1) :
    u ≠ ∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ)) := by sorry
