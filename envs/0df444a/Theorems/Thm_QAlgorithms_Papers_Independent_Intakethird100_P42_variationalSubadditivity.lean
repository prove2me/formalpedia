-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_variationalSubadditivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.variationalSubadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:12:51.144756+00:00
-- url     : https://prove2.me/theorems/a1c5dbcf-2974-4200-bf09-9367c41ca7f9
-- title:
--   Unnumbered result: subadditivity and existence of the regularized variational limit
-- statement:
--   Let $\{p(x),\rho_x^B\}$ be a normalized finite memoryless classical–quantum source. Let $d:X\times X\to[0,\infty)$ be a finite distortion measure and $D\ge0$ a distortion target. For each positive integer $n$, define $V_n(D)$ by minimizing $(I(X^n;Y)-I(Y;B^n))/n$ over every finite nonempty classical auxiliary alphabet, every stochastic channel $W(y\mid x^n)$, and every $y$-controlled reconstruction POVM on $B^n$, subject to expected average per-letter distortion at most $D$. All states and Born probabilities are computed from these data, and entropies are in bits. Use value $+\infty$ when the feasible set is empty.
--
--   Then for all positive $m,n$,
--   $$(m+n)V_{m+n}(D)\le mV_m(D)+nV_n(D),\qquad \lim_{n\to\infty}V_n(D)\text{ exists in }[0,+\infty].$$
--   Whenever $V_n(D)<+\infty$, its minimum is attained by a feasible channel and reconstruction POVM.
--
--   This concerns only the regularized variational sequence. It does not identify the limit with the literal exact-distortion operational quantity in the defective Theorem 4.2.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 16, Unnumbered result: subadditivity and existence of the regularized variational limit

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.16, paragraph following Theorem 4.2: subadditivity and existence of the
regularized VARIATIONAL limit, with finite minima attained. No equality with the
literal operational rate-distortion definition (which has an endpoint defect) is claimed. -/
theorem variationalSubadditivity {X B : Type} [Fintype X] [Fintype B]
    [Nonempty X] [Nonempty B] (E : CQData X B) (hE : E.Valid)
    (d : X → X → ℝ) (hd : ∀ x z, 0 ≤ d x z) (D : ℝ) (hD : 0 ≤ D) :
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      ((m + n : ℕ) : ℝ≥0∞) * blockRD E d D (m + n) ≤
        (m : ℝ≥0∞) * blockRD E d D m + (n : ℝ≥0∞) * blockRD E d D n) ∧
    (∃ L : ℝ≥0∞, Tendsto (fun n : ℕ => blockRD E d D (n + 1)) atTop (nhds L)) ∧
    (∀ n : ℕ, 1 ≤ n → blockRD E d D n ≠ ⊤ →
      ∃ P : RDDatum X B n, rdExpected E d P ≤ D ∧
        ENNReal.ofReal (auxCost (iidCQ E n) P.auxiliary / n) = blockRD E d D n) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
