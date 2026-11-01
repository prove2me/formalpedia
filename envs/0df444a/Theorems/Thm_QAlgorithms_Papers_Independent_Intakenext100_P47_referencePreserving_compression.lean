-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_referencePreserving_compression
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.referencePreserving_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:19:34.322923+00:00
-- url     : https://prove2.me/theorems/56d0c4ac-6ef4-43ec-857b-2c6908321789
-- title:
--   Remark III.3: entropy exchange is a reference-preserving noise-compression rate
-- statement:
--   Fix a density matrix $\rho_{AB}$ on finite nonzero spaces and a coordinated local product-unitary map $T$. For every $\epsilon>0$ there exists $n_0\ge1$ such that for every $n\ge n_0$ there is a COLUR ensemble $R_n$ with $N_n$ actual product-unitary terms for which
--
--   $$\log_2N_n\le n\bigl(S_e(T,\rho)+\epsilon\bigr),\qquad\bigl\|(\mathrm{id}_Z\otimes R_n)(\psi)-(\mathrm{id}_Z\otimes T^{\otimes n})(\psi)\bigr\|_1\le\epsilon.$$
--
--   The error test holds for any finite purifying reference $Z$ and any normalized purification $\psi$ of the fixed source $\rho^{\otimes n}$; the ensemble is chosen before that purification. The tensor-power channel is evaluated on all matrix units. This gives the reference-preserving noise-compression meaning of entropy exchange for a fixed source.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 7, Remark III.3: entropy exchange is a reference-preserving noise-compression rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Remark III.3: compression tested jointly with every finite purifying reference.
The approximating ensemble is chosen before the purification, not uniformly over other inputs. -/
theorem referencePreserving_compression {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (T : COLUR A B) (eps : ℝ) (heps : 0 < eps) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ R : COLUR (Copies A n) (Copies B n),
        Real.logb 2 R.count ≤ (n : ℝ) * (entropyExchange T.operation rho + eps) ∧
        ∀ (Z : Type) [Fintype Z] [Nonempty Z]
          (psi : EuclideanSpace ℂ (Z × (Copies A n × Copies B n))), IsState psi →
          traceLeft (pureDensity psi) = sourcePower rho n →
          traceNorm (idTensorSuperop R.operation (pureDensity psi) -
            idTensorSuperop (regroupedChannelPower T.operation n) (pureDensity psi)) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
