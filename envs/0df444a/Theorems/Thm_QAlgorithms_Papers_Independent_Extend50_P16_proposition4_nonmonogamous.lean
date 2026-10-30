-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_proposition4_nonmonogamous
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.proposition4_nonmonogamous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:03:35.902044+00:00
-- url     : https://prove2.me/theorems/46a7b2ec-676c-4c55-8178-bc9050e1f4b7
-- title:
--   Exact PPT cost is not monogamous
-- statement:
--   Let $|\psi\rangle_{ABC}=(|000\rangle+|011\rangle+\sqrt2|110\rangle)/2$ be the specified unit vector of three qubits. Let $\psi_{A:BC}=|\psi\rangle\langle\psi|$, and obtain $\psi_{AB}$ and $\psi_{AC}$ by tracing out $C$ and $B$, respectively. For the deterministic exact PPT preparation cost,
--
--   $$
--   E_{\mathrm{PPT}}(\psi_{A:BC})=1,\qquad
--   E_{\mathrm{PPT}}(\psi_{AB})=E_{\mathrm{PPT}}(\psi_{AC})=\log_2(3/2),\qquad
--   E_{\mathrm{PPT}}(\psi_{AB})+E_{\mathrm{PPT}}(\psi_{AC})>E_{\mathrm{PPT}}(\psi_{A:BC}).
--   $$
--
--   All three density operators are normalized. This is an explicit failure of monogamy across the cut $A:BC$.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 4, Proposition 4 (No monogamy): exact PPT cost

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Proposition 4, evaluated on p.21 (S89)-(S94): strict failure
of monogamy for marginals of the fixed normalized state, with whole cut A:BC. -/
theorem proposition4_nonmonogamous :
    IsDensityMatrix monogamyWhole ∧ IsDensityMatrix monogamyAB ∧
    IsDensityMatrix monogamyAC ∧
    exactCost monogamyWhole = 1 ∧
    exactCost monogamyAB = logTwoReal (3 / 2) ∧
    exactCost monogamyAC = logTwoReal (3 / 2) ∧
    exactCost monogamyWhole < exactCost monogamyAB + exactCost monogamyAC := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
