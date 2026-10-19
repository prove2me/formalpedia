-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P54_local_pinching_penalty
-- name    : QAlgorithms.Papers.Independent.Information100.P54.local_pinching_penalty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:07:58.526031+00:00
-- url     : https://prove2.me/theorems/f9639de3-3d63-425b-b126-297bb4697eb0
-- title:
--   Lemma 2 (Local pinching penalty)
-- statement:
--   Let $\zeta$ be a normalized state on two nonzero finite-dimensional registers $A,B$. Let $(P_k)$ be mutually orthogonal self-adjoint projections on $B$ with $\sum_kP_k=I_B$. Define the local pinching $\mathcal P(\zeta)=\sum_k(I_A\otimes P_k)\zeta(I_A\otimes P_k)$ and the outcome probabilities $p_k=\operatorname{Tr}[(I_A\otimes P_k)\zeta]$. With relative entropy, Shannon entropy and relative entropy of entanglement measured in bits,
--
--   $$E_R(\zeta)\le E_R(\mathcal P\zeta)+D(\zeta\Vert\mathcal P\zeta)\le E_R(\mathcal P\zeta)+H(p).$$
--
--   This bounds the entanglement contribution of local measurement coherence without asserting recovery of that coherence.
-- source:
--   Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels, arXiv:2610.06832v1, PDF p. 9, Lemma 2 (Local pinching penalty)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

noncomputable section

open scoped ENNReal Matrix

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P54

/-- arXiv:2610.06832v1, PDF p.9, Lemma 2, Eq.(A13): both pinching inequalities.
Local Hilbert spaces are nonzero and finite-dimensional. -/
theorem local_pinching_penalty {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [Nonempty I] [Nonempty J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (P : K → Matrix J J ℂ) (hself : ∀ k, (P k).conjTranspose = P k)
    (hproj : ∀ k, P k * P k = P k)
    (horth : ∀ k l, k ≠ l → P k * P l = 0) (hcomplete : ∑ k, P k = 1) :
    relativeEntanglement rho ≤ relativeEntanglement (bobPinching P rho) +
      relativeEntropyBits rho (bobPinching P rho) ∧
    relativeEntanglement (bobPinching P rho) + relativeEntropyBits rho (bobPinching P rho) ≤
      relativeEntanglement (bobPinching P rho) + shannonEntropy (pinchingProbability P rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P54

end
