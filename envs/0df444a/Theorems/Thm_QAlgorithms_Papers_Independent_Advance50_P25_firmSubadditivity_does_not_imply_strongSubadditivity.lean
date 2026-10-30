-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_firmSubadditivity_does_not_imply_strongSubadditivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.firmSubadditivity_does_not_imply_strongSubadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:59:19.270909+00:00
-- url     : https://prove2.me/theorems/db7c4216-c67f-4ecc-8016-a4498dca1081
-- title:
--   Firm subadditivity need not imply strong subadditivity
-- statement:
--   Let $S_Q(\rho)=1-\operatorname{Tr}\rho^2$ on normalized finite-dimensional complex density operators. Define $I_Q(a:b)=S_Q(\rho_a)+S_Q(\rho_b)-S_Q(\rho_{ab})$ using actual partial traces, and let $\chi_Q(P_a,b)$ be the measurement Holevo quantity for a finite POVM $P_a$. Then
--
--   $$
--   S_Q\text{ is firmly subadditive},\qquad
--   S_Q\text{ is not strongly subadditive in the sense of Eq.(4)}.
--   $$
--
--   Explicitly, $\chi_Q(P_a,b)\le I_Q(a:b)$ for every finite bipartite density and every such POVM, whereas there exists a finite tripartite density with $I_Q(a:bc)<I_Q(a:b)$.
--
--   The SSA form is the source’s mutual-information monotonicity under discarding a subsystem; no equivalence with other entropy-linear-combination formulations is assumed for general entropies.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 5, §VIII, unnumbered separation: FSA does not imply SSA

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.5, §VIII: quadratic entropy separates FSA from exactly the SSA form (4). -/
theorem firmSubadditivity_does_not_imply_strongSubadditivity :
    FirmlySubadditive quadraticEntropy ∧ ¬ StronglySubadditive quadraticEntropy := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end
