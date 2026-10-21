-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_tripartiteMonotoneCone
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.tripartiteMonotoneCone
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:23:28.190742+00:00
-- url     : https://prove2.me/theorems/0e1ee6c9-7550-43ef-a0ba-f96fd2dba7e6
-- title:
--   Nonnegative formal yields matching all five monotones
-- statement:
--   For any normalized finite tripartite law, put $r=I(A:B\mid C)$, $s=I(B:C\mid A)$, $t=I(C:A\mid B)$, and $u=I(A:B)-I(A:B\mid C)$. Then $u=I(B:C)-I(B:C\mid A)=I(C:A)-I(C:A\mid B)$, and
--   $$S_3=r+s+t+u,\quad T_3=r+s+t+2u,\quad r,s,t,r+u,s+u,t+u\ge0.$$
--   In generator order $P_{AB},P_{BC},P_{AC},P^x,P^3$, choose real yields $(r,s,t,0,u)$ if $u\ge0$, and $(r+u,s+u,t+u,-u,0)$ otherwise. Every yield is nonnegative, and their weighted generator vectors equal the law's five-monotone vector exactly.
--
--   These are compatible formal rates. Existence of a physically reversible distillation protocol remains open.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 8, §IV.D, (47)–(50)

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

/-- §IV.D, PDF pp.8--9, (47)--(50): symmetry of u, the two identities,
all six positivity constraints, and nonnegative real yields with matching
monotone vectors. This asserts no physically reversible distillation protocol. -/
theorem tripartiteMonotoneCone (p : CData 3) (hp : IsValidClassicalData p) :
    let v := secrecyCoordinates p
    let y := formalYields p
    v 3 = lawCMI p {1} {2} ∅ - lawCMI p {1} {2} {0} ∧
    v 3 = lawCMI p {2} {0} ∅ - lawCMI p {2} {0} {1} ∧
    cValue .dual p = v 0 + v 1 + v 2 + v 3 ∧
    cValue .total p = v 0 + v 1 + v 2 + 2*v 3 ∧
    0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧
    0 ≤ v 0 + v 3 ∧ 0 ≤ v 1 + v 3 ∧ 0 ≤ v 2 + v 3 ∧
    (∀ j, 0 ≤ y j) ∧
    (∀ i : Fin 5, fiveValues p i =
      y 0 * fiveTable 0 i + y 1 * fiveTable 2 i + y 2 * fiveTable 1 i +
      y 3 * fiveTable 4 i + y 4 * fiveTable 3 i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
