-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_quantum_conditioning_strict
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.quantum_conditioning_strict
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:36:02.011928+00:00
-- url     : https://prove2.me/theorems/82460f95-2525-49a1-8c19-7999393fa481
-- title:
--   Theorem 3(b): quantum conditioning is strictly richer than classical conditioning
-- statement:
--   Quantum conditioning is strictly richer than finite classical conditioning. There is a joint law of classical variables $X,M,Y$ with alphabet sizes $24,6,18$, respectively, and a four-dimensional quantum extension $F$, such that
--
--   $$
--   (H(X\mid F),H(M\mid F),H(Y\mid F))=(\log_2 6,\log_2 6,\log_2 18),
--   $$
--
--   and no finite classical extension $C$ of that same law has this conditional-entropy triple. In particular, all three universal assertions of Theorem 3(a) are false. There is also a finite law $q(x,y,z)$, a finite quantum channel $X\to F$, and a maximizing finite classical channel $X\to C_*$ for which
--
--   $$
--   I(C_*;Y)-I(C_*;Z)<I(F;Y)-I(F;Z),\qquad
--   I(C;Y)-I(C;Z)\le I(C_*;Y)-I(C_*;Z)
--   $$
--
--   for every finite classical channel $X\to C$. Both optimization extensions factor through $X$, so $F-X-YZ$ and $C-X-YZ$. No such factorization is required of arbitrary points of the entropy hull. All states and laws are normalized, and all information quantities are in bits.
--
--   This gives an entropy-region separation and a strict quantum advantage in the auxiliary optimization, without asserting any uniform quantum dimension bound.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 10, Theorem 3(b): quantum conditioning is strictly richer than classical conditioning

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Theorem 3(b), PDF pp.10,13–15, and consequence (8). The witness sizes are 24,6,18;
the quantum witness has dimension four and entropies log2(6),log2(6),log2(18). -/
theorem quantum_conditioning_strict :
    (∃ p : Law (Alphabet 3 ![24, 6, 18]),
      (∃ Q : QChannel (Alphabet 3 ![24, 6, 18]) (Fin 4),
        ∀ i, qCond p.prob Q.rho (fun x => x i) =
          (![Real.logb 2 6, Real.logb 2 6, Real.logb 2 18] : Fin 3 → ℝ) i) ∧
      (p.prob, ![Real.logb 2 6, Real.logb 2 6, Real.logb 2 18]) ∉ classicalHull 3 ![24, 6, 18]) ∧
    ¬ AssertionOne ∧ ¬ AssertionTwo ∧ ¬ AssertionThree ∧
    (∃ n y z d k : ℕ, 0 < n ∧ 0 < y ∧ 0 < z ∧ 0 < d ∧ 0 < k ∧
      ∃ p : Law (Fin n × Fin y × Fin z), ∃ Q : QChannel (Fin n) (Fin d),
      ∃ K : CChannel (Fin n) (Fin k), classicalDifference p K < quantumDifference p Q ∧
        ∀ l : ℕ, 0 < l → ∀ L : CChannel (Fin n) (Fin l),
          classicalDifference p L ≤ classicalDifference p K) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
