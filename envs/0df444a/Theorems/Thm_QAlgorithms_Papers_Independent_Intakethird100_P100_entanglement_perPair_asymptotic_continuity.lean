-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P100_entanglement_perPair_asymptotic_continuity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P100.entanglement_perPair_asymptotic_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:26:19.725374+00:00
-- url     : https://prove2.me/theorems/c29c3b14-2fcc-4440-b61a-599780bea8bd
-- title:
--   Asymptotic continuity of entanglement per pair
-- statement:
--   Fix a density matrix $\rho'$ on a positive finite-dimensional bipartite space $H_A\otimes H_B$. For every integer $n\geq1$, let $\omega_n$ be any density matrix on $H_A^{\otimes n}\otimes H_B^{\otimes n}$. Group all Alice factors and all Bob factors when forming the tensor power $(\rho')^{\otimes n}$. Let $E$ denote either the relative entropy of entanglement or the infimum of relative entropy over normalized PPT states, always across this grouped bipartition and using natural logarithms. If the full trace distance tends to zero, then, for both choices of $E$,
--
--   $$
--   \bigl\|(\rho')^{\otimes n}-\omega_n\bigr\|_1\longrightarrow0
--   \quad\Longrightarrow\quad
--   \frac1n\left|E\bigl((\rho')^{\otimes n}\bigr)-E(\omega_n)\right|\longrightarrow0.
--   $$
--
--   The fixed target may be mixed, and the approximants may have arbitrary correlations. This expresses continuity of entanglement per pair in the many-copy limit.
--
--   **Formalization Note** The sequence is indexed by $n=k+1$ to keep every denominator positive. Both entropic infima are finite in every finite-copy space. The accepted infima are stored in bits; the Lean per-copy expression includes the factor $\log 2$ to express the displayed natural-logarithm convention.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, PDF p. 1, Introduction, equation (1), and the PPT variation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P100

noncomputable section

open Filter

open scoped ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P100

open QAlgorithms.Papers.Independent.Dependency50.P15
  (relativeDistance relativeDistanceValue positiveOperatorRelativeEntropyBits groupedTensorPower)

open QAlgorithms.Papers.Independent.Information100.P54
  (relativeEntropyBits relativeEntanglement)

/-- Introduction (1), PDF p.1, including the PPT variation asserted there:
trace-norm approximation of a fixed tensor-power target gives vanishing
entanglement difference per pair. Positive copy counts k+1 remove division
by zero. The approximants can be correlated and the fixed target can be mixed. -/
theorem entanglement_perPair_asymptotic_continuity
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rhoPrime : Matrix (A × B) (A × B) ℂ)
    (hrhoPrime : IsDensityMatrix rhoPrime)
    (approx : (k : ℕ) →
      Matrix ((Fin (k + 1) → A) × (Fin (k + 1) → B))
        ((Fin (k + 1) → A) × (Fin (k + 1) → B)) ℂ)
    (happrox : ∀ k, IsDensityMatrix (approx k))
    (hclose : Tendsto
      (fun k : ℕ => traceNorm (groupedTensorPower rhoPrime (k + 1) - approx k))
      atTop (nhds 0)) :
    Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) * Real.log 2 *
      |(relativeEntanglement (groupedTensorPower rhoPrime (k + 1))).toReal -
        (relativeEntanglement (approx k)).toReal|) atTop (nhds 0) ∧
    Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) * Real.log 2 *
      |(pptEntanglement (groupedTensorPower rhoPrime (k + 1))).toReal -
        (pptEntanglement (approx k)).toReal|) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P100

end
