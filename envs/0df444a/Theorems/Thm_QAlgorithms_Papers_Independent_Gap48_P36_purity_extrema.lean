-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_purity_extrema
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.purity_extrema
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:53:57.055643+00:00
-- url     : https://prove2.me/theorems/6595f856-3d86-46aa-a655-2373dd32e2b3
-- title:
--   Corollary 4: equal output purity extrema
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. For a channel $\Phi$, any chosen conjugate, and every real $p\ge1$,
--
--   $$
--   \nu_p(\Phi)=\nu_p(\Phi^C),\qquad S_{\min}(\Phi)=S_{\min}(\Phi^C).
--   $$
--
--   Thus both output purity extrema are conjugation invariants.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 8, Corollary 4: equal output purity extrema

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

/-- Corollary 4, PDF p.8: maximal output finite-p norm and minimal output entropy. -/
theorem purity_extrema [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (PhiC : Superop A C) (hPhi : IsChannel Phi)
    (hc : CPComplementary Phi PhiC) (p : ℝ) (hp : 1 ≤ p) :
    nu (ENNReal.ofReal p) Phi = nu (ENNReal.ofReal p) PhiC ∧ hmin Phi = hmin PhiC := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
