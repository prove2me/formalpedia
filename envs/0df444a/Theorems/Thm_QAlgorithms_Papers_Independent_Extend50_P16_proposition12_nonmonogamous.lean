-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_proposition12_nonmonogamous
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.proposition12_nonmonogamous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:06:21.579991+00:00
-- url     : https://prove2.me/theorems/e602afe9-a95b-479f-aab8-d45f380b8331
-- title:
--   Kappa-entanglement is not monogamous
-- statement:
--   Let $|\psi\rangle_{ABC}=(|000\rangle+|011\rangle+\sqrt2|110\rangle)/2$, and let $\psi_{AB}$ and $\psi_{AC}$ be the reduced density operators of its pure density $\psi_{A:BC}$. All three operators are normalized. With $E_N(\rho)=\log_2\|T_B(\rho)\|_1$ for the relevant bipartition,
--
--   $$
--   E_\kappa(\psi_{A:BC})=1,\qquad
--   E_\kappa(\psi_{AB})=E_N(\psi_{AB})=\log_2(3/2),\qquad
--   E_\kappa(\psi_{AC})=E_N(\psi_{AC})=\log_2(3/2),
--   $$
--   $$
--   E_\kappa(\psi_{AB})+E_\kappa(\psi_{AC})>E_\kappa(\psi_{A:BC}).
--   $$
--
--   The example distinguishes the two-qubit marginals from the cut between a qubit and the joint four-dimensional system $BC$.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 21, Proposition 12 (No monogamy): kappa-entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.21, Proposition 12, (S89)-(S94): the computed marginals both
have entanglement log_2(3/2), whereas the A:BC value is one. -/
theorem proposition12_nonmonogamous :
    IsDensityMatrix monogamyWhole ∧ IsDensityMatrix monogamyAB ∧
    IsDensityMatrix monogamyAC ∧
    kappaEntanglement monogamyWhole = 1 ∧
    kappaEntanglement monogamyAB = logTwoReal (3 / 2) ∧
    kappaEntanglement monogamyAC = logTwoReal (3 / 2) ∧
    bipartiteLogNegativity monogamyAB = logTwoReal (3 / 2) ∧
    bipartiteLogNegativity monogamyAC = logTwoReal (3 / 2) ∧
    kappaEntanglement monogamyWhole < kappaEntanglement monogamyAB + kappaEntanglement monogamyAC := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
