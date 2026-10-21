-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_fiveLawValues
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.fiveLawValues
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:20:14.57322+00:00
-- url     : https://prove2.me/theorems/03b40f44-27e9-463f-8c42-c0a28983a148
-- title:
--   All five monotone values on five laws
-- statement:
--   Let $P_{AB},P_{AC},P_{BC}$ be a uniform shared bit on the indicated pair, with the third party constant. Let $P^3$ be uniform on $000,111$, and let $P^x$ be uniform on $000,110,101,011$. These are normalized three-bit laws. In column order $I(A:BC),I(B:AC),I(C:AB),S_3,T_3$ and row order $P_{AB},P_{AC},P_{BC},P^3,P^x$, the values in bits are
--   $$\begin{pmatrix}1&1&0&1&1\\1&0&1&1&1\\0&1&1&1&1\\1&1&1&1&2\\1&1&1&2&1\end{pmatrix}.$$
--   This states all 25 entries for the explicit laws, not for abstract entropy profiles.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 7, §IV.B, (41)–(45), table

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- §IV.B, PDF p.7, (41)--(45) and table: all 25 entries of the five
monotones on the five explicitly constructed laws, ordered AB, AC, BC, 3, xor. -/
theorem fiveLawValues : ∀ j : Fin 5,
    IsValidClassicalData (exampleLaw j) ∧ ∀ i : Fin 5, fiveValues (exampleLaw j) i = fiveTable j i := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
