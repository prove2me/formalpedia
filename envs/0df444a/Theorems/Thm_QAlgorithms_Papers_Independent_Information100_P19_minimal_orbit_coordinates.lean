-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_minimal_orbit_coordinates
-- name    : QAlgorithms.Papers.Independent.Information100.P19.minimal_orbit_coordinates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:49:15.244398+00:00
-- url     : https://prove2.me/theorems/173c6840-82da-408d-8ae5-d1f6739a5bdf
-- title:
--   Theorem 4.5
-- statement:
--   Let $O_n$ be the orbits of permutation pairs under simultaneous conjugation and simultaneous inversion, with no exchange of the local factors. Summing coefficients on orbits is onto and its kernel is exactly the universal separable evaluation kernel. Its image of $I_n^{\rm sep}$ is precisely the cone of coefficients nonnegative on every separable evaluation. In particular, these coordinates are minimal. Their number is
--   $$b_n=\frac1{2n!}\sum_{g\in S_n}\left[\left(\sum_\chi\chi(g)^2\right)^2+\left(\sum_\chi\chi(g)\right)^3\right],$$
--   with sums over distinct irreducible characters. For $n=1,\ldots,8$ the counts are $1,4,11,43,155,761,4043,27190$. The count formula is credited by the source to BD14, Proposition 3.2.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 22, Theorem 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Theorem 4.5; arXiv:2609.29471v1, PDF pp.22, 23. -/
theorem minimal_orbit_coordinates (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (@reduce n) ∧
    (∀ f : TensorCoeff n, reduce f = 0 ↔
      ∀ a b, 0<a → 0<b → ∀ X : Bip a b,
        QAlgorithms.Entanglement.IsSeparablePositive X → tensorEval f X = 0) ∧
    (∀ f : TensorCoeff n, f ∈ sepCone n ↔ reduce f ∈ reducedSepCone n) ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian →
      ∀ p : Perms n, orbitEval (Quot.mk orbitRel p) X = (tensorTrace p X).re) ∧
    ((Nat.card (Orbit n) : ℝ) =
      (1 / (2*(Nat.factorial n : ℝ))) *
        ∑ g : Equiv.Perm (Fin n),
          ((∑ᶠ χ : IrredChar n, (χ.val g).re^2)^2 +
           (∑ᶠ χ : IrredChar n, (χ.val g).re)^3)) ∧
    ([Nat.card (Orbit 1),Nat.card (Orbit 2),Nat.card (Orbit 3),Nat.card (Orbit 4),
      Nat.card (Orbit 5),Nat.card (Orbit 6),Nat.card (Orbit 7),Nat.card (Orbit 8)] =
      [1,4,11,43,155,761,4043,27190]) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
