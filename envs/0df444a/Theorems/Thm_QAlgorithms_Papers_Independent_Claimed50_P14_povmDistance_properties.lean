-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_povmDistance_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.povmDistance_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:27:36.665751+00:00
-- url     : https://prove2.me/theorems/4dfb8b0a-315f-4ed5-b3ed-308ba93909a7
-- title:
--   Pure-state squared distance between finite POVMs
-- statement:
--   Let $h,m\ge1$, and let $P=(P_i)_{i=1}^m$ and $Q=(Q_i)_{i=1}^m$ be POVMs on $\mathbb C^h$: all effects are positive semidefinite and their sums are the identity. With normalized unitarily invariant measure on unit vectors, put
--
--   $$D(P,Q)=\int\sum_{i=1}^m |\langle\psi|(P_i-Q_i)|\psi\rangle|^2\,d\psi.$$
--
--   Then $D(P,Q)\ge0$, and $D(P,Q)=0$ if and only if $P_i=Q_i$ for every $i$. For any further POVM $Q'$ and $0\le t\le1$,
--
--   $$D(P,tQ+(1-t)Q')\le tD(P,Q)+(1-t)D(P,Q').$$
--
--   For every unitary $V$, simultaneous conjugation of both POVMs by $V$ preserves $D$. Outcome count $m$ and Hilbert dimension $h$ are independent. This is the paper's distance criterion, without a triangle-inequality claim.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 3, Lemma 1 (Distance criterion for two POVMs)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF p.3, Lemma 1 and (15)-(16). No triangle inequality is asserted.
The number of outcomes m need not equal the Hilbert dimension h. -/
theorem povmDistance_properties {h m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (P Q : Fin m → (Matrix (Fin h) (Fin h) ℂ)) (hP : IsPOVM P) (hQ : IsPOVM Q) :
    0 ≤ povmDistance hh P Q ∧
    (povmDistance hh P Q = 0 ↔ ∀ i, P i = Q i) ∧
    (∀ Q2 : Fin m → (Matrix (Fin h) (Fin h) ℂ), IsPOVM Q2 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      povmDistance hh P ((t : ℂ) • Q + ((1-t : ℝ) : ℂ) • Q2) ≤
        t*povmDistance hh P Q + (1-t)*povmDistance hh P Q2) ∧
    (∀ U : Matrix.unitaryGroup (Fin h) ℂ,
      povmDistance hh (fun i => (U : (Matrix (Fin h) (Fin h) ℂ))*P i*(U : (Matrix (Fin h) (Fin h) ℂ))ᴴ)
        (fun i => (U : (Matrix (Fin h) (Fin h) ℂ))*Q i*(U : (Matrix (Fin h) (Fin h) ℂ))ᴴ) = povmDistance hh P Q) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
