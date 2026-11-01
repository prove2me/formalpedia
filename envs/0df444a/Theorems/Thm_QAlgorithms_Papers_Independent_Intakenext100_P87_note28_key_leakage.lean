-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_note28_key_leakage
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.note28_key_leakage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:19:45.742894+00:00
-- url     : https://prove2.me/theorems/e528eb7e-4399-4c3b-93d4-fec6b3ee068f
-- title:
--   Note [28]: high singlet fidelity implies small key leakage
-- statement:
--   There are constants $C>0$ and $k_0>0$, independent of the key length, state, measurement, and reference dimension, with the following property. For $R\ge1$ and real $k\ge k_0$, let $\rho_{ABE}$ be any normalized joint state with $AB$ squared overlap with $R$ singlets greater than $1-2^{-k}$. Alice and Bob generate a key along any common axis, and Eve may perform any delayed generalized measurement. For Alice's key $K$ and Eve's outcome $Y$,
--
--   $$I(K:Y)\le2^{-k}\left(2R+k+\frac1{\ln2}\right)+C2^{-2k}.$$
--
--   The leading term equals $2^{-c}$ for $c=k-\log_2(2R+k+1/\ln2)$. This is accessible classical information; its dependence on $R$ is retained.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 14, Note [28]: high singlet fidelity implies small key leakage

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF pp.14--15, note [28]: uniform large-k expansion. The main term is exactly
2^(-c), c = k - log2(2R+k+1/ln 2); it retains dependence on the key length R.
All reference dimensions and delayed Eve measurements are unrestricted. -/
theorem note28_key_leakage :
    ∃ C : ℝ, 0 < C ∧ ∃ k0 : ℝ, 0 < k0 ∧
      ∀ (R : ℕ), 0 < R → ∀ (k : ℝ), k0 ≤ k →
      ∀ {E Y : Type} [Fintype E] [DecidableEq E] [MeasurableSpace Y]
        (rho : Matrix (PairRegister R × E) (PairRegister R × E) ℂ),
      IsDensityMatrix rho →
      1 - (2 : ℝ) ^ (-k) < singletOverlap (traceRight rho) →
      ∀ (U : Matrix.unitaryGroup Bool ℂ) (Q : OperatorPOVM E Y),
      keyLeakage rho U Q ≤ ENNReal.ofReal
        ((2 : ℝ) ^ (-k) * (2 * R + k + 1 / Real.log 2) + C * (2 : ℝ) ^ (-2 * k)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
