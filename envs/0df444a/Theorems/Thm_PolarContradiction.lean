-- Prove2me | Theorems.Thm_PolarContradiction
-- name    : PolarContradiction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:39:21.511803+00:00
-- url     : https://prove2.me/theorems/690c55b1-3af3-4d63-aed7-5cbd2332d778
-- title:
--   Polar Contradiction: Polar Contradiction
-- statement:
--   The whole Section-3 inequality chain below eq:polar, as pure real
--   arithmetic: under exactly the scalar facts the geometry layer delivers, the
--   eq:polar right-hand side is strictly negative.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/PolarContradiction.lean#L13-L73
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/PolarContradiction.lean#L13-L73

module
public import Definitions.Def_PHarmonicPoly_ABound
public import Definitions.Def_PHarmonicPoly_AbsorbK
public import Definitions.Def_PHarmonicPoly_Endgame
public import Definitions.Def_PHarmonicPoly_PolarContradiction
public import Theorems.Thm_ABound
public import Theorems.Thm_AbsorbK
public import Theorems.Thm_Endgame

set_option autoImplicit false
@[expose] public section
public section
open Real

theorem PolarContradiction {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) (p a b c q κ : ℝ)
    (hp : (n : ℝ) - 1 / 13 ≤ p) (hpn : p ≤ (n : ℝ))
    (ha : 8 / 13 < a) (ha1 : a ≤ 1)
    (hq : q = a ^ 2 + b ^ 2) (hq1 : q ≤ 1)
    (hbc : b ^ 2 + c ^ 2 ≤ 1)
    (hk0 : 0 ≤ κ) (hk : κ ≤ 1 / Real.pi) :
    c - (p - 1 + ((n : ℝ) - p) / m) * a + ((n : ℝ) - 2) * κ * b
        + (p - 2) * (b ^ 2 * (c - a) / q) < 0 := by sorry
