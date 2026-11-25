-- Prove2me | Theorems.Thm_TrigPolyZeroCount
-- name    : TrigPolyZeroCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:31:55.434428+00:00
-- url     : https://prove2.me/theorems/469cf205-2d76-472f-bd31-f7a814c22511
-- title:
--   Trig Poly Zero Count: Trig Poly Zero Count
-- statement:
--   Zero counting for a nonzero real trigonometric polynomial of degree at most
--   `m`: over one half-open period, a finite set `Z` of zeros together with a
--   separate double zero at `t₁` forces `#Z + 2 ≤ 2*m`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyZeroCount.lean#L11-L167
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyZeroCount.lean#L11-L167

module
public import Definitions.Def_PHarmonicPoly_TrigPolyToComplexPoly
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_TrigPolyZeroCount
public import Theorems.Thm_TrigPolySmooth
public import Theorems.Thm_TrigPolyToComplexPoly

set_option autoImplicit false
@[expose] public section
public section

theorem TrigPolyZeroCount {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hTne : ∃ s : ℝ, T s ≠ 0)
    {t₀ : ℝ} {Z : Finset ℝ}
    (hZmem : ∀ z ∈ Z, z ∈ Set.Ico t₀ (t₀ + 2 * Real.pi))
    (hZzero : ∀ z ∈ Z, T z = 0)
    {t₁ : ℝ} (ht₁mem : t₁ ∈ Set.Ico t₀ (t₀ + 2 * Real.pi)) (ht₁notZ : t₁ ∉ Z)
    (ht₁zero : T t₁ = 0) (ht₁deriv : deriv T t₁ = 0) :
    Z.card + 2 ≤ 2 * m := by sorry
