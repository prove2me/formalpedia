-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_hashingInequality
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.hashingInequality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:10:14.20625+00:00
-- url     : https://prove2.me/theorems/67c41ffe-8d96-49ce-8610-20ee0f7013d8
-- title:
--   Theorem 10: hashing inequality
-- statement:
--   Let $\rho^{AB}$ be an arbitrary normalized density matrix on finite complex registers of positive dimension. Its operational one-way EPR distillation capacity satisfies
--
--   $$D_{\to}(\rho)\ge H(\rho^B)-H(\rho^{AB})=I_c(A\rangle B)_\rho.$$
--
--   Here the entropies are in bits. A protocol on $n$ independent copies consists of a finite CP instrument $(\mathcal T_\ell)$ on Alice, whose sum is trace preserving, and a CPTP map $\mathcal R_\ell$ on Bob chosen using Alice's public message. Its evaluated output is $\sum_\ell(\mathcal T_\ell\otimes\mathcal R_\ell)(\rho^{\otimes n})$, without any additional shared state. Achievable rates have $M_n\ge1$, squared fidelity to the normalized maximally entangled state $\Phi_{M_n}$ tending to one, and $\log_2M_n/n$ tending to the rate for protocols defined for every $n$; $D_{\to}$ is their supremum.
--
--   This is the hashing lower bound, including nonpositive coherent information. A purification or a successful coherent protocol is constructed in the proof and is not an extra hypothesis.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 7, Theorem 10

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF p.7, Theorem 10 (Hashing inequality),
operational definitions p.6. A purification used in the proof is not a hypothesis.
Nonpositive coherent information gives only a vacuous lower bound. -/
theorem hashingInequality {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Op (A × B))
    (h : QAlgorithms.IsDensityMatrix rho) :
    coherentInfo rho ≤ entCapacity rho := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
