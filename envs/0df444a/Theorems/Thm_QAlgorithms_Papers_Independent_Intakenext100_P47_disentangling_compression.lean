-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_disentangling_compression
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.disentangling_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:18:49.014288+00:00
-- url     : https://prove2.me/theorems/45b14a51-c3f3-4d8a-8aeb-7b4f54cf22e7
-- title:
--   Proposition III.2: randomness compression for an exactly disentangling block
-- statement:
--   Let $\rho_{AB}$ be a density matrix on finite nonzero spaces and let $k\ge1$. Fix a coordinated local product-unitary map $T$ on $k$ copies such that the constructed output $\sigma=T(\rho^{\otimes k})$ is separable. For every $\epsilon>0$ there exists $n_0\ge1$ such that for every $n\ge n_0$ a uniform coordinated product-unitary ensemble $R$ on $kn$ copies, with $N$ terms, satisfies
--
--   $$\|R(\rho^{\otimes kn})-\sigma^{\otimes n}\|_1\le\epsilon,\qquad\log_2N\le n\bigl(S(\sigma)-kS(\rho)+\epsilon\bigr).$$
--
--   Tensor copies of $\sigma$ are explicitly regrouped in the same party order as the $kn$-copy input. In particular, $R$ $\epsilon$-disentangles this input. This compresses the randomness needed to reproduce an exactly disentangling block asymptotically.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 6, Proposition III.2: randomness compression for an exactly disentangling block

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

/-- PDF pp.6--7, Proposition III.2: the input contains k*n copies, not n copies. -/
theorem disentangling_compression {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (k : ℕ) (hk : 0 < k)
    (T : COLUR (Copies A k) (Copies B k))
    (hT : Entanglement.IsSeparableDensity (T.operation (sourcePower rho k)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ R : COLUR (Copies A (k*n)) (Copies B (k*n)),
        (∀ i, R.weight i = (R.count : ℝ)⁻¹) ∧
        traceNorm (R.operation (sourcePower rho (k*n)) -
          (Matrix.of fun (x y : Copies A (k*n) × Copies B (k*n)) => ∏ t : Fin n,
            T.operation (sourcePower rho k)
              ((fun s => x.1 (blockIndex t s)),
                (fun s => x.2 (blockIndex t s)))
              ((fun s => y.1 (blockIndex t s)),
                (fun s => y.2 (blockIndex t s))))) ≤ eps ∧
        Disentangles (R.operation (sourcePower rho (k*n))) eps ∧
        Real.logb 2 R.count ≤ (n : ℝ) *
          (vnEntropy (T.operation (sourcePower rho k)) - k * vnEntropy rho + eps) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
