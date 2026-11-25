-- Prove2me | Theorems.Thm_SphereMaxNormalize
-- name    : SphereMaxNormalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:27:41.673693+00:00
-- url     : https://prove2.me/theorems/17990f7c-c71a-4dfa-bab4-5724b813155f
-- title:
--   Sphere Max Normalize: Sphere Max Normalize
-- statement:
--   The paper's normalization: a nonzero homogeneous `P` can be rescaled by a
--   single nonzero constant so that it attains the value `1` at a unit vector `e`
--   and is bounded by `1` in absolute value on the whole unit sphere, without
--   changing whether `EpAlg p` vanishes.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/SphereMaxNormalize.lean#L13-L81
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/SphereMaxNormalize.lean#L13-L81

module
public import Definitions.Def_PHarmonicPoly_EpAlgSmul
public import Definitions.Def_PHarmonicPoly_MvPolyContDiff
public import Definitions.Def_PHarmonicPoly_SphereMaxNormalize
public import Theorems.Thm_EpAlgSmul
public import Theorems.Thm_MvPolyContDiff

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem SphereMaxNormalize {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (p : ℝ)
    {P : MvPolynomial (Fin n) ℝ} (hP : P ≠ 0) (hhom : P.IsHomogeneous m) :
    ∃ (c : ℝ) (e : EuclideanSpace ℝ (Fin n)), c ≠ 0 ∧ ‖e‖ = 1
      ∧ MvPolynomial.eval (fun i => e i) (c • P) = 1
      ∧ (∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
          |MvPolynomial.eval (fun i => y i) (c • P)| ≤ 1)
      ∧ (EpAlg p (c • P) = 0 ↔ EpAlg p P = 0) := by sorry
