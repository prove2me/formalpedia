-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_conjugation_preserves_purity
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.conjugation_preserves_purity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:51:07.503109+00:00
-- url     : https://prove2.me/theorems/be99bc8e-8b32-400d-b625-8acf16cf643c
-- title:
--   Theorem 5 / paper headline: conjugation preserves multiplicativity and entropy additivity
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. Let $\Phi_1,\Phi_2$ be channels with chosen conjugates $\Phi_1^C,\Phi_2^C$, and $p\ge1$ real.
--
--   $$
--   \begin{aligned}\nu_p(\Phi_1\otimes\Phi_2)=\nu_p(\Phi_1)\nu_p(\Phi_2)&\iff\nu_p(\Phi_1^C\otimes\Phi_2^C)=\nu_p(\Phi_1^C)\nu_p(\Phi_2^C),\\S_{\min}(\Phi_1\otimes\Phi_2)=S_{\min}(\Phi_1)+S_{\min}(\Phi_2)&\iff S_{\min}(\Phi_1^C\otimes\Phi_2^C)=S_{\min}(\Phi_1^C)+S_{\min}(\Phi_2^C).\end{aligned}
--   $$
--
--   Both purity questions transfer to the chosen conjugates, with tensor channels acting on all joint inputs.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 8, Theorem 5 / paper headline: conjugation preserves multiplicativity and entropy additivity

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

/-- Theorem 5, PDF p.8: both channel iff statements, for chosen conjugates. -/
theorem conjugation_preserves_purity [Nonempty A] [Nonempty B] [Nonempty C]
    [Nonempty A2] [Nonempty B2] [Nonempty C2]
    (Phi : Superop A B) (Psi : Superop A2 B2)
    (PhiC : Superop A C) (PsiC : Superop A2 C2)
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (hc : CPComplementary Phi PhiC) (hd : CPComplementary Psi PsiC)
    (p : ℝ) (hp : 1 ≤ p) :
    (Multiplicative (ENNReal.ofReal p) Phi Psi ↔ Multiplicative (ENNReal.ofReal p) PhiC PsiC) ∧
    (Additive Phi Psi ↔ Additive PhiC PsiC) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
