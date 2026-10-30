-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_two_circle_decision
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.two_circle_decision
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:37:30.61484+00:00
-- url     : https://prove2.me/theorems/d7e178b5-3c1b-42a3-8fa6-5a7ca3759d5c
-- title:
--   V B 2: decision between two uniformly phased pure-state circles
-- statement:
--   Choose distinct $\alpha_0,\alpha_1\in[0,\pi)$, let $b$ be uniform on $\{0,1\}$ and $\theta$ uniform on $[0,2\pi)$, and prepare $n\ge1$ copies of $|\psi(\theta,b)\rangle=\cos(\alpha_b/2)|0\rangle+e^{i\theta}\sin(\alpha_b/2)|1\rangle$. For every normalized POVM $M$ there is a product-basis measurement followed by stochastic processing, described by a POVM $N$, such that for each $b$ and measurable $B$,
--   $$\frac1{2\pi}\int_0^{2\pi}\operatorname{tr}(M(B)\psi(\theta,b)^{\otimes n})\,d\theta
--   =\operatorname{tr}(N(B)D_b^{\otimes n}),\quad D_b=\operatorname{diag}(\cos^2(\alpha_b/2),\sin^2(\alpha_b/2)).$$
--   Here $\psi(\theta,b)$ denotes the pure density matrix. These are the conditional laws given $b$, so all relevant performance values are preserved.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 23, V B 2: decision between two uniformly phased pure-state circles

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.23-24, V B 2: all b-conditioned outcome probabilities are
reproducible by measuring Z separately and processing the results. The
comparison averages the common unknown phase; it is not pointwise in theta. -/
theorem two_circle_decision {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) (a : Fin 2 → ℝ)
    (ha : ∀ b, 0 ≤ a b ∧ a b < Real.pi) (hne : a 0 ≠ a 1)
    (M : Measurements.OperatorPOVM (Fin n → Fin 2) O) :
    ∃ N : Measurements.OperatorPOVM (Fin n → Fin 2) O, BasisProcessing n N ∧
      ∀ b : Fin 2, ∀ B, MeasurableSet B →
        phaseAverage (fun theta => effectProb (M.operator B) (piKron n (circleDensity (a b) theta))) =
          effectProb (N.operator B) (piKron n (circleDiagonal (a b))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
