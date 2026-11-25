-- Prove2me | Theorems.Thm_PHarmonicPoly_main_theorem
-- name    : PHarmonicPoly.main_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:46:57.772+00:00
-- url     : https://prove2.me/theorems/49a0ffb9-3a59-5a35-b539-672abff570ae
-- title:
--   PHarmonic Poly: main theorem
-- statement:
--   **Theorem 1.1.** Let `n ≥ 3` and `p ≥ n - 1/13`. Every real polynomial `u` on `ℝⁿ`
--   with `E_p(u) = |Du|² Δu + (p - 2) ⟨D²u Du, Du⟩ = 0` everywhere is affine.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/Solution.lean#L23-L29
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/Solution.lean#L23-L29

module
public import Definitions.Def_PHarmonicPoly
public import Definitions.Def_PHarmonicPoly_Solution
set_option autoImplicit false
@[expose] public section
public section
open PHarmonicPoly
open MvPolynomial

theorem PHarmonicPoly.main_theorem {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c := by sorry
