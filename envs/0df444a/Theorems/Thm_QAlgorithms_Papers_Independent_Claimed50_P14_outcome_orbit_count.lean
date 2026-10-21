-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_outcome_orbit_count
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.outcome_orbit_count
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:30:44.478068+00:00
-- url     : https://prove2.me/theorems/4227b20d-0e2e-4246-9c25-b5e2c1716e24
-- title:
--   Outcome equality patterns classify the relabeling orbits
-- statement:
--   Let $d,N\ge1$, and consider strings of $N+1$ labels in $\{1,\ldots,d\}$, including the replica label. Two strings $x,y$ are related by one simultaneous label permutation if and only if
--
--   $$x_a=x_b\quad\Longleftrightarrow\quad y_a=y_b\qquad\text{for every pair of positions }a,b.$$
--
--   Consequently the number of orbits equals the number of partitions of the $N+1$ positions into at most $d$ nonempty parts. All partitions occur when $d\ge N+1$; footnote [12] prints this inequality backwards. This counts label patterns, not permutations of source calls.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 5, §IV, Eqs.(33)–(34): outcome equality patterns and orbit count

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.5-6, (33)-(34): orbit count = partitions with at most d parts.
Footnote [12] on p.12 reverses the Bell-number condition; all partitions
are available when d >= N+1. -/
theorem outcome_orbit_count (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (∀ x y : Labels d (N+1), (outcomeOrbit d N).r x y ↔
      ∀ a b, (x a = x b ↔ y a = y b)) ∧
    Nat.card (Quotient (outcomeOrbit d N)) = Nat.card (BoundedPartitions d N) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
