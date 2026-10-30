-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_symmetric_measurement
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.symmetric_measurement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:22:35.965997+00:00
-- url     : https://prove2.me/theorems/34973e3b-095c-4371-9aa1-9d7c1bf74721
-- title:
--   Proposition 3.4: symmetric measurement and covariant implemented channel
-- statement:
--   Let $d,N\ge1$, and fix a PBT protocol whose unit pure resource has the simultaneous permutation and conjugate-unitary symmetries of Proposition 3.3. There is another POVM $\{E'_i\}$ with exactly the same resource such that
--   $$ (I\otimes P_\pi)E'_i(I\otimes P_\pi)^\dagger=E'_{\pi(i)},\qquad (U\otimes\overline U^{\otimes N})E'_i(U\otimes\overline U^{\otimes N})^\dagger=E'_i.$$
--   The implemented channel $\Lambda'$ is covariant: $\Lambda'(X)=U\Lambda'(U^\dagger XU)U^\dagger$ for every $U\in U(d)$ and every input operator $X$. Fidelity does not decrease, diamond error does not increase, and every convex invariant channel cost does not increase. These are all four source clauses and its stated cost extension.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 15, Proposition 3.4: symmetric measurement and covariant implemented channel

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Proposition 3.4, PDF pp.15–16, all four clauses, plus the stated convex-cost
extension. The shared resource remains fixed and the replacement channel is implemented. -/
theorem symmetric_measurement {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    (P : PBTProtocol d N (Ports d N)) (hP : SymmetricPurification P.resource) :
    ∃ Q : PBTProtocol d N (Ports d N), Q.resource = P.resource ∧
      (∀ pi : Equiv.Perm (Fin N), ∀ i,
        conjSuperop (Matrix.kronecker (1 : Op (Fin d)) (QAlgorithms.Schur.tensorPermutation d N pi)) (Q.measurement i) =
          Q.measurement (pi i)) ∧
      (∀ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ i,
        conjSuperop (Matrix.kronecker (U : Op (Fin d))
          (QAlgorithms.Papers.Independent.Information100.P63.tensorPower N (fun a b => conj ((U : Op (Fin d)) a b))))
          (Q.measurement i) = Q.measurement i) ∧
      (∀ U : Matrix.unitaryGroup (Fin d) ℂ, conjugateChannel U Q.channel = Q.channel) ∧
      NoWorse Q.channel P.channel := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
