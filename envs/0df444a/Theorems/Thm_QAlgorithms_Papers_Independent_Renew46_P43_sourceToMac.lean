-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_sourceToMac
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.sourceToMac
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:45:00.360985+00:00
-- url     : https://prove2.me/theorems/24e7d7b6-1be7-494a-8429-323e92846c1d
-- title:
--   Theorem III.5: For lambdaBar,delta>0 and independent P1,P2, any length-n quantum-side-information code of rates Rbar_i and error≤lambdaBar for th
-- statement:
--   Let $W$ be a two-sender finite classical-input MAC with independent sender laws $P_1,P_2$. Choose finite normalized pure decompositions $W_{x_1x_2}=\sum_\pi q(\pi\mid x_1,x_2)\pi$ and form the correlated source law $P_1(x_1)P_2(x_2)q(\pi\mid x_1,x_2)$. For $\bar\lambda,\delta>0$, any length-$n$ source code of rates $\bar R_i$ and average error at most $\bar\lambda$, with free $Y^n$ at its decoder, yields an actual MAC code satisfying:
--
--   $$
--   \bar e_{\rm MAC}\le4\bar\lambda,\qquad R_i\ge H(P_i)-\bar R_i-\delta\quad(i=1,2),\quad n\ge n_0(|X_1|,|X_2|,\delta).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 43, Theorem III.5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Theorem III.5, PDF p.43: source/channel reduction for TWO independent classical
sender laws. The source is constructed from the channel's finite pure decompositions;
the decoder's free side-information register is Y^n. -/
theorem sourceToMac (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, ∀ (C : QAlgorithms.Papers.Independent.Claimed50.P40.ClassicalChannel 2),
      C.alphabet = a →
      ∀ (P : QAlgorithms.Papers.Independent.Claimed50.P40.InputLaw C.alphabet)
        (b : ℕ) (hb : 0 < b) (pi : Fin b → Matrix (Fin C.output) (Fin C.output) ℂ)
        (hpure : ∀ j, IsPure (pi j) ∧ InBlocks C.block (pi j))
        (hdistinct : Function.Injective pi)
        (q : (∀ i, Fin (C.alphabet i)) → PMF (Fin b)),
      (∀ x, C.state x = ∑ j, ((q x j).toReal : ℂ) • pi j) →
      ∀ (n : ℕ), n0 ≤ n → ∀ (lambda : ℝ), 0 < lambda →
      ∀ c : SideCode (macReductionSource C P b hb pi hpure hdistinct q) n,
      c.error ≤ lambda →
      ∃ d : QAlgorithms.Papers.Independent.Claimed50.P40.MultiwayBlockCode
        (QAlgorithms.Papers.Independent.Claimed50.P40.singleReceiver C) n,
        QAlgorithms.Papers.Independent.Claimed50.P40.averageTupleError d 0 ≤ 4 * lambda ∧
        ∀ i, QAlgorithms.Papers.Independent.Claimed50.P40.codeRate d i ≥
          pmfEntropy (P i) - c.rate i - delta := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
