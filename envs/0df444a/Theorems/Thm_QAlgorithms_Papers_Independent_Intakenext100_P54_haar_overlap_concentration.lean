-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_haar_overlap_concentration
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.haar_overlap_concentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:34:39.372507+00:00
-- url     : https://prove2.me/theorems/cba1085d-9658-4e1f-9c11-8a53e5359152
-- title:
--   Lemma 3: Haar overlap concentration
-- statement:
--   Let $D,K\ge1$, let $0\le p\le D$ be an integer, let $\phi$ be a normalized pure state on $\mathbb C^D$, and let $P$ be an orthogonal projector of rank $p$. Suppose $U_1,\ldots,U_K$ are independent measurable random unitaries, each having the normalized Haar law. For $0<\varepsilon\le1$,
--
--   $$\Pr\left\{\left|\frac1K\sum_{k=1}^K\operatorname{Tr}(U_k\phi U_k^*P)-\frac pD\right|\ge\frac{\varepsilon p}{D}\right\}\le 2\,2^{-Kp\varepsilon^2/6}.$$
--
--   Here a vector and its rank-one density operator are distinguished in the formalization. The result controls Haar overlap fluctuations; at rank zero the event has probability one and the upper bound is two.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 3, Lemma 3: Haar overlap concentration

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

/-- Lemma 3, PDF pp.3,14–15: two-sided concentration of independent Haar overlaps.
Rank zero is included; its right-hand side is two. The paper's exp has base two. -/
theorem haar_overlap_concentration {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (D K p : ℕ)
    (hD : 0 < D) (hK : 0 < K) (hp : p ≤ D)
    (phi : RSPVector (Fin D)) (P : Matrix (Fin D) (Fin D) ℂ)
    (hHerm : P.IsHermitian) (hProj : P * P = P) (hRank : P.trace.re = p)
    (U : Fin K → Omega → Matrix.unitaryGroup (Fin D) ℂ)
    (hMeas : ∀ k, Measurable (U k)) (hInd : iIndepFun U mu)
    (hHaar : ∀ k, Measure.map (U k) mu = QAlgorithms.Schur.unitaryHaar D)
    (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    mu {w | |(∑ k, ((U k w : Matrix (Fin D) (Fin D) ℂ) * pureDensity phi.val *
      (U k w : Matrix (Fin D) (Fin D) ℂ)ᴴ * P).trace.re) /
      (K : ℝ) - (p : ℝ) / D| ≥ eps * p / D} ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ (-(K : ℝ) * p * eps ^ 2 / 6)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
