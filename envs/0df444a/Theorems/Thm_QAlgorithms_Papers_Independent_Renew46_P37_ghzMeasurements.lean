-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_ghzMeasurements
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.ghzMeasurements
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:27:23.75762+00:00
-- url     : https://prove2.me/theorems/ae56c61b-1226-4c31-a0a5-576d475f7566
-- title:
--   GHZ measurements and all six monotone values
-- statement:
--   For the normalized plus GHZ state, independent local computational $z$ measurements give $P^3$, uniform on $000,111$. Independent standard Hadamard $x$ measurements give $P^x$, uniform on the four even-parity strings. In bits,
--   $$S_3(\mathrm{GHZ})=T_3(\mathrm{GHZ})=3,\quad(S_3,T_3)(P^3)=(1,2),\quad(S_3,T_3)(P^x)=(2,1).$$
--   Consequently, $S_3(P^3)+T_3(P^3)=S_3(P^x)+T_3(P^x)=[S_3(\mathrm{GHZ})+T_3(\mathrm{GHZ})]/2$.
--
--   The positive GHZ phase and standard Hadamard convention fix even parity.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 11, §V.D, (66),(67)

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

/-- §V.D, PDF p.11, (66),(67): z gives the common-bit law and Hadamard x
gives the even-parity xor law; all six values and the half-sum identity. -/
theorem ghzMeasurements :
    ghzMeasurement false = exampleLaw 3 ∧ ghzMeasurement true = exampleLaw 4 ∧
    info .dual (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3 ∧
    info .total (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3 ∧
    cValue .dual (exampleLaw 3) = 1 ∧ cValue .total (exampleLaw 3) = 2 ∧
    cValue .dual (exampleLaw 4) = 2 ∧ cValue .total (exampleLaw 4) = 1 ∧
    cValue .dual (exampleLaw 3) + cValue .total (exampleLaw 3) =
      cValue .dual (exampleLaw 4) + cValue .total (exampleLaw 4) ∧
    cValue .dual (exampleLaw 3) + cValue .total (exampleLaw 3) =
      (info .dual (pureDensity (ghzVector 3)) (singleParties 3) ∅ +
       info .total (pureDensity (ghzVector 3)) (singleParties 3) ∅) / 2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
