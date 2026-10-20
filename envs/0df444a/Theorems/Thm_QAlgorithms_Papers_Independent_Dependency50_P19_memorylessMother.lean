-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_memorylessMother
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.memorylessMother
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:09:34.297162+00:00
-- url     : https://prove2.me/theorems/2b764078-a66e-48a4-b0c1-f6369d6e7c94
-- title:
--   FQSW: joint state transfer and entanglement distillation
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Fix a pure state $\phi^{RAB}$. Alice receives $A^n$, Bob receives $B^n$, and $R^n$ is untouched. For every error $\epsilon>0$ and rate slack $\delta>0$, all sufficiently large integers $n$ admit local CPTP encoding and decoding operations, a forward message $Q$ and a retained entanglement register $L$, such that
--
--   $$
--   \log_2 d_Q\le n\bigl(\tfrac12 I(A;R)_\phi+\delta\bigr),\qquad
--   \log_2 d_L\ge n\bigl(\tfrac12 I(A;B)_\phi-\delta\bigr),
--   $$
--
--   and the complete output is within $\epsilon$ of $\phi^{\otimes n}$ transferred to Bob, jointly tensor a maximally entangled state of local dimension $d_L$. Only $Q$ is communicated, and no entanglement assistance is supplied. The threshold and the code may depend on the fixed source and the two tolerances.
--
--   This is the simultaneous transfer and distillation conclusion of the mother protocol.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 3, Eq. (2); Sections II, VII

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq.(2), PDF p.3, established on pp.12–13: simultaneous state transfer and
entanglement distillation from a fixed normalized i.i.d. source. -/
theorem memorylessMother {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi) :
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      MotherCode (pureDensity phi) n
        (mutualInformation (marginalRA (pureDensity phi))/2)
        (mutualInformation (traceLeft (pureDensity phi))/2) eps delta := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
