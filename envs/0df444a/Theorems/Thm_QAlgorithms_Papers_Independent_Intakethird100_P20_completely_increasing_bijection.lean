-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_completely_increasing_bijection
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.completely_increasing_bijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:32:05.906116+00:00
-- url     : https://prove2.me/theorems/474c2bd3-6cfc-4027-a27a-ca99f52b711c
-- title:
--   completely-increasing-bijection
-- statement:
--   For a complete lattice $L$, write $H_a=\{b:a\le b\}$ for $a\ne0$. Bounded completely increasing functions on $L\setminus\{0\}$ correspond bijectively to abstract observable functions on $D(L)$ under the explicit inverse maps
--
--   $$r\longmapsto \bigl(J\longmapsto\inf_{a\in J}r(a)\bigr),\qquad f\longmapsto\bigl(a\longmapsto f(H_a)\bigr).$$
--
--   Here complete increase means preservation of suprema of every nonempty family of nonzero elements. The topology and intersection condition defining abstract observables are the membership topology and nonempty-family condition. This is a complete-lattice result; orthomodularity is not required.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 11, completely-increasing-bijection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- completely-increasing-bijection; de Groote, Observables I, PDF p./pp. 11, 12.
-/
theorem completely_increasing_bijection {L : Type u} [CompleteLattice L] :
    (∀ r : {a : L // a ≠ ⊥} → ℝ,
      BddAbove (Set.range r) → BddBelow (Set.range r) → IsCompletelyIncreasing r →
      IsAbstractObservable (extendIncreasing r) ∧ restrictObservable (extendIncreasing r) = r) ∧
    (∀ f : DualIdeal L → ℝ, IsAbstractObservable f →
      BddAbove (Set.range (restrictObservable f)) ∧ BddBelow (Set.range (restrictObservable f)) ∧
      IsCompletelyIncreasing (restrictObservable f) ∧ extendIncreasing (restrictObservable f) = f) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
