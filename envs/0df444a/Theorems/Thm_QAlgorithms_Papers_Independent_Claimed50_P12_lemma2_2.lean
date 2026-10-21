-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemma2_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemma2_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:31:30.803898+00:00
-- url     : https://prove2.me/theorems/066f9527-6c70-4848-b3b6-8f297237cd38
-- title:
--   Exponentially accurate dominated approximants
-- statement:
--   Let $\rho$ be a density operator, $\sigma\ge0$ on a nonzero finite-dimensional complex Hilbert space, and $s\in\mathbb R$ with $D(\rho\|\sigma)<s$, where $D$ is normalized base-two relative entropy. There exist $\kappa>0$ and operators $\bar\rho_n\ge0$, chosen as one sequence, such that for every positive integer $n$, $\operatorname{tr}\bar\rho_n\le1$, and
--
--   $$\bar\rho_n\le2^{sn}\sigma^{\otimes n},\qquad \lim_{n\to\infty}2^{n\kappa}\Delta(\bar\rho_n,\rho^{\otimes n})=0.$$
--
--   Here $\Delta$ is the generalized trace distance of Eq.17. The constants are independent of the copy count; this is the converse typicality construction to Lemma 2.1.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 6, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma 2.2 (PDF p.6): constants before n, base-two decay, initial zeros allowed. -/
theorem lemma2_2 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef)
    (s : ℝ) (hs : normalizedRelativeEntropyBits rho sigma < (s : EReal)) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ bar : (n : ℕ) → Op (Fin (n+1) → I),
      (∀ n, (bar n).PosSemidef ∧ (bar n).trace.re ≤ 1 ∧
        OperatorLE (bar n) (((2 : ℝ) ^ (s * ((n+1 : ℕ) : ℝ)) : ℂ) • matrixPower sigma (n+1))) ∧
      Tendsto (fun n => (2 : ℝ) ^ (((n+1 : ℕ) : ℝ) * kappa) *
        generalizedTraceDistance (bar n) (matrixPower rho (n+1))) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
