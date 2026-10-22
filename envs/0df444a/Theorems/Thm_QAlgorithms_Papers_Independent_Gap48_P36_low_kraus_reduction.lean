-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_low_kraus_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.low_kraus_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:54:42.903011+00:00
-- url     : https://prove2.me/theorems/98632769-51c4-4bfb-8578-1545abf2d952
-- title:
--   Theorem 6: reduction to low-Kraus-rank enlarged-output channels
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. Fix positive integers $d_i,e_i$ for $i=1,2$ and real $p\ge1$. Suppose multiplicativity at this exponent holds for every pair $\Psi_i:M_{d_i}\to M_{d_i e_i}$ with minimum Kraus number at most $e_i$. Then every pair of channels $\Phi_i:M_{d_i}\to M_{e_i}$ satisfies
--
--   $$
--   \nu_p(\Phi_1\otimes\Phi_2)=\nu_p(\Phi_1)\nu_p(\Phi_2).
--   $$
--
--   The dimensions are fixed before the universal premise; the Kraus bound is the output dimension $e_i$.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 9, Theorem 6: reduction to low-Kraus-rank enlarged-output channels

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Theorem 6, PDF pp.9–10: dimensions are fixed before the universal premise;
the enlarged-output maps have Kraus number at most dprime, not d. -/
theorem low_kraus_reduction (d1 d2 e1 e2 : ℕ)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (he1 : 0 < e1) (he2 : 0 < e2)
    (p : ℝ) (hp : 1 ≤ p)
    (hsmall : ∀ (Psi1 : Superop (Fin d1) (Fin (d1 * e1)))
      (Psi2 : Superop (Fin d2) (Fin (d2 * e2))),
      IsChannel Psi1 → IsChannel Psi2 → krausNumber Psi1 ≤ e1 → krausNumber Psi2 ≤ e2 →
      Multiplicative (ENNReal.ofReal p) Psi1 Psi2) :
    ∀ (Phi1 : Superop (Fin d1) (Fin e1)) (Phi2 : Superop (Fin d2) (Fin e2)),
      IsChannel Phi1 → IsChannel Phi2 → Multiplicative (ENNReal.ofReal p) Phi1 Phi2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
