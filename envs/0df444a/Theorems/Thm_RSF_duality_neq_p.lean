-- Prove2me | Theorems.Thm_RSF_duality_neq_p
-- name    : RSF.duality_neq_p
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-23T03:13:39.043699+00:00
-- url     : https://prove2.me/theorems/ab8a10b1-9fdf-47f0-b4a0-6e2e3226b0cc
-- title:
--   Poincare duality for l different from p (Theorem 1.1.1, the Berkovich-Huber case)
-- statement:
--   Theorem 1.1.1 of the thesis in the case l different from p, proved by Berkovich and by Huber: if K is an algebraically closed non-archimedean field of mixed characteristic (0, p) and X is a proper smooth rigid-analytic variety of pure dimension d over K, then for every prime l different from p and every integer i there is a natural perfect pairing between H^i(X_et, F_l) and H^(2d-i)(X_et, F_l) with values in the Tate object F_l(-d) - the cohomology is Poincare dual to its complementary degree. The milestone states the duality over the rigid cohomology interface: the pairing exists in every degree, is bilinear in both arguments, nondegenerate in both arguments, and exhaustive. This is the literature anchor for the goal, which treats the remaining case l = p.
--
--   **Formalization Note** The base field, the variety, and the cohomology groups are abstract interface data carrying the geometric conditions as labels; constructing them for actual rigid-analytic varieties and establishing the labeled hypotheses is part of the proposed work.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), Theorem 1.1.1 for l different from p; V. G. Berkovich, Etale cohomology for non-Archimedean analytic spaces, Publ. Math. IHES 78 (1993); R. Huber, Etale Cohomology of Rigid Analytic Varieties and Adic Spaces, Vieweg (1996).

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

namespace RSF

/-!  Theorem 1.1.1 of the thesis in the case ell different from p, proved by
Berkovich and Huber: on a proper smooth rigid-analytic variety of pure
dimension d over an algebraically closed non-archimedean field of mixed
characteristic (0, p), the etale cohomology with coefficients in F_ell
admits, in every degree, a pairing against the complementary degree with
values in the Tate object F_ell(-d) which is bilinear in both arguments,
nondegenerate in both arguments, and exhaustive. This is the literature
anchor for the goal of the mission, which treats the remaining case
ell = p.  -/

theorem duality_neq_p : ∀ w : RigidCohWorld,
    w.ℓ ≠ w.P →
    w.nonarchField → w.algClosed → w.mixedChar →
    w.properSmooth → w.pureDim →
    ∃ pair : ∀ i : ℤ, w.H (2 * (w.d : ℤ) - i) → w.H i → w.Tate,
      (∀ (i : ℤ) (x y : w.H (2 * (w.d : ℤ) - i)) (z : w.H i),
        pair i (w.add (2 * (w.d : ℤ) - i) x y) z = w.tadd (pair i x z) (pair i y z)) ∧
      (∀ (i : ℤ) (k : ZMod w.ℓ) (x : w.H (2 * (w.d : ℤ) - i)) (z : w.H i),
        pair i (w.smul (2 * (w.d : ℤ) - i) k x) z = w.tsmul k (pair i x z)) ∧
      (∀ (i : ℤ) (x : w.H (2 * (w.d : ℤ) - i)) (y z : w.H i),
        pair i x (w.add i y z) = w.tadd (pair i x y) (pair i x z)) ∧
      (∀ (i : ℤ) (k : ZMod w.ℓ) (x : w.H (2 * (w.d : ℤ) - i)) (z : w.H i),
        pair i x (w.smul i k z) = w.tsmul k (pair i x z)) ∧
      (∀ (i : ℤ) (x : w.H (2 * (w.d : ℤ) - i)),
        (∀ z : w.H i, pair i x z = w.tzero) → x = w.zero (2 * (w.d : ℤ) - i)) ∧
      (∀ (i : ℤ) (z : w.H i),
        (∀ x : w.H (2 * (w.d : ℤ) - i), pair i x z = w.tzero) → z = w.zero i) ∧
      (∀ (i : ℤ) (φ : ZModLinear w.ℓ (w.H i) w.Tate
            (w.add i) (w.zero i) (w.smul i) w.tadd w.tzero w.tsmul),
        ∃ u : w.H (2 * (w.d : ℤ) - i), ∀ z : w.H i, pair i u z = φ.map z) := by
  sorry

end RSF
