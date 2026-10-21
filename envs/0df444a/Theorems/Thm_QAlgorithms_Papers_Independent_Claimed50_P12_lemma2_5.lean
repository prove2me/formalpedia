-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemma2_5
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemma2_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:45:40.72235+00:00
-- url     : https://prove2.me/theorems/10d46a44-7bbb-4eb9-a9f9-0af4b759ae6f
-- title:
--   Entropy-window asymptotic equipartition
-- statement:
--   Let $\rho$ be a density operator on a nonzero finite-dimensional complex Hilbert space, and let $\delta>0$. Write $H(\rho)$ for its entropy in bits. Let $m_n$ be the total spectral weight of $\rho^{\otimes n}$ in the closed interval $[2^{-n(H(\rho)+\delta)},2^{-n(H(\rho)-\delta)}]$. Then
--
--   $$m_n\longrightarrow1,\qquad \exists c,C>0\;\exists N\;\forall n\ge N:\ |m_n-1|\le C e^{-cn}.$$
--
--   This is the typical spectral mass statement used in the recovery argument. Constants may depend on $\rho$ and $\delta$, and are chosen before $n$.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 7, Lemma 2.5

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

/-- Lemma 2.5, Eq.42 (PDF pp.7–8): actual convergence and exponential speed. -/
theorem lemma2_5 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Op I) (hrho : IsDensityMatrix rho) (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun n => entropyWindowMass rho (n+1) delta) atTop (nhds 1) ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      |entropyWindowMass rho (n+1) delta - 1| ≤ C * Real.exp (-c * ((n+1 : ℕ) : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
