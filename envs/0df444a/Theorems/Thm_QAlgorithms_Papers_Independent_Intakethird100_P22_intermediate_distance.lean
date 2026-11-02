-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_intermediate_distance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.intermediate_distance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:02:43.012752+00:00
-- url     : https://prove2.me/theorems/1c8df5f4-e6a8-48a4-994c-74afb21a4989
-- title:
--   Lemma 1: real versus intermediate distance equals correctness error
-- statement:
--   Let $P^{\rm pass}_{S_A S_B T E\mid Z}$ be a normalized classical-device law with a common finite nonempty key alphabet $\mathcal K$ and finite nonempty transcript, Eve-output and Eve-input alphabets. The $(S_A,S_B,T)$ marginal is independent of $Z$. The ideal pass law replaces the keys by a uniform perfectly correlated pair, independent of the actual $(T,E\mid Z)$ marginal. The intermediate law copies Alice's key into Bob's register and preserves $(S_A,T,E\mid Z)$. Let $r\in[0,1]$ be the abort probability, with an identical normalized abort branch in all three systems. Write $d_{\rm NS}$ for the operational NS distance, and $s,c,k$ for the pass-weighted secrecy, disagreement and security errors, respectively. Thus $s=(1-r)d_{\rm NS}(P_{S_A T E\mid Z}^{\rm pass},P_{S_A T E\mid Z}^{\rm ideal,pass})$, $c=(1-r)\Pr[S_A\ne S_B\mid\mathrm{pass}]$, and $k=(1-r)d_{\rm NS}(P^{\rm pass},P^{\rm ideal,pass})$.
--
--   For the real and intermediate full output systems,
--
--   $$d_{\rm NS}(P^{\rm real},P^{\rm int})=c=(1-r)\Pr[S_A\ne S_B\mid\mathrm{pass}].$$
--
--   The intermediate system isolates correctness error while keeping Alice and Eve's actual marginal.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 31, Lemma 1 / equations (94), (104)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

/-- PDF pp.31–32, Lemma 1, (94),(104): NS distance to the constructed intermediate
system equals the weighted disagreement probability. -/
theorem intermediate_distance {K T E Z : Type}
    [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    [Nonempty K] [Nonempty T] [Nonempty E] [Nonempty Z]
    (r : KeyOutput K T E Z) (z : Z) :
    cdDistance (withAbort r.abortProbability r.abort r.pass)
      (withAbort r.abortProbability r.abort (intermediateKey r.pass)) = correctnessError r z := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
