-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_finite_probabilistic_exact_pi
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.finite_probabilistic_exact_pi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:36:48.131247+00:00
-- url     : https://prove2.me/theorems/49fcc66b-736d-45e7-8e0e-0b90955e5c28
-- title:
--   Theorem 5: finite probabilistic exact protocol Pi
-- statement:
--   Let $D\ge1$ and $0<\varepsilon\le1$. Put $B=(10/\varepsilon)^2D\log_2(20D/\varepsilon)$. There are $1\le K\le B$ randomising unitaries for which the following protocol uses one shared maximally entangled state of rank $D$. On a normalized target $|\psi\rangle$, Alice measures
--
--   $$A_k=\frac{D}{K(1+\varepsilon)}U_k\overline\psi U_k^*,\qquad A_{\rm fail}=I-\sum_k A_k,$$
--
--   announces the outcome, and Bob applies $U_k^\top$ on good outcome $k$. The effects form a POVM. The unnormalized corrected good branch equals $\psi/[K(1+\varepsilon)]$, so the conditional output is exactly $\psi$, and
--
--   $$\Pr\{\mathrm{failure}\}=\frac{\varepsilon}{1+\varepsilon}\le\varepsilon,\qquad C=\log_2(K+1)\le\log_2(B+1),\qquad E=\log_2D.$$
--
--   The construction works for every target with the same unitaries. This is a finite probabilistic exact RSP protocol.
--
--   **Formalization Note** The complete message support includes failure. The displayed cbit bound corrects the printed bound that counts only good messages.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 4, Theorem 5: finite probabilistic exact protocol Pi

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Theorem 5, PDF pp.3–4: the specified Pi protocol, its exact good branches and exact
failure probability. Correction to printed bookkeeping: the complete support has K+1 outcomes,
so the support communication bound is log2(randomisingBound+1), using log2 D ebits. -/
theorem finite_probabilistic_exact_pi (D : ℕ) (hD : 0 < D)
    (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ (K : ℝ) ≤ randomisingBound D eps ∧
      Real.logb 2 (K + 1 : ℝ) ≤ Real.logb 2 (randomisingBound D eps + 1) ∧
      ∃ U : Fin K → Matrix.unitaryGroup (Fin D) ℂ,
        Randomising U eps ∧ ∀ psi : RSPVector (Fin D),
          IsPOVM (piEffect U eps psi) ∧
          (∀ k, piBranch U eps psi (some k) =
            ((1 / ((K : ℝ) * (1 + eps)) : ℝ) : ℂ) • pureDensity psi.val) ∧
          (piBranch U eps psi none).trace.re = eps / (1 + eps) ∧
          eps / (1 + eps) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
