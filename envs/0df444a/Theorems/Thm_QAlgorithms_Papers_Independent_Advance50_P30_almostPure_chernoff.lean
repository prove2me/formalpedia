-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_almostPure_chernoff
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.almostPure_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:58:07.118517+00:00
-- url     : https://prove2.me/theorems/2a937f68-e856-4879-be6f-9f2c696e9b8c
-- title:
--   Lemma 2: cited Chernoff bound for pure almost-power states
-- statement:
--   Let $n,w\ge1$, $2r\le n$, and let $\theta$ be a unit vector in a finite-dimensional complex Hilbert space. Let $\psi$ be a unit symmetric almost-power vector along $\theta$ as in Definition 1, and let $M$ be a normalized $w$-outcome POVM. For every $\delta>0$, the actual product-measurement Born law satisfies $$\Pr\{\|P_M(|\theta\rangle\langle\theta|)-Q_M(|\psi\rangle\langle\psi|)\|_1>\delta\}\le 2^{-n(\delta^2/4-H_2(r/n))+w\log_2(n/2+1)}.$$ Here $Q_M$ is the normalized empirical frequency and $H_2$ is binary entropy in bits. This is the cited Renner result, not a new contribution of this paper.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 14, Appendix Lemma 2: cited Renner generalized Chernoff bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF p.14, Lemma 2, cited Theorem 4.5.2 of Renner (17).
The pure almost-power result is retained as cited background, with the exact
full-L1 event and exponent used by this paper. -/
theorem almostPure_chernoff {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (theta : Vec I) (n r w : ℕ) (hn : 0 < n) (hr : 2 * r ≤ n) (hw : 0 < w)
    (psi : Vec (Copies I n)) (hpsi : AlmostPure theta n r psi)
    (E : Fin w → Op I) (hE : IsPOVM E) (delta : ℝ) (hdelta : 0 < delta) :
    iidEvent (pureDensity psi) E (fun out =>
      l1 (fun a => effectProb (E a) (pureDensity theta)) (empiricalFrequency out) > delta) ≤
        chernoffError delta n r w := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
