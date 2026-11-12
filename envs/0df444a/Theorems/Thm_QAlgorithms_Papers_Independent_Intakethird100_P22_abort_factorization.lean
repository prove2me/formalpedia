-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_abort_factorization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.abort_factorization
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T08:01:50.742436+00:00
-- url     : https://prove2.me/theorems/965deb6b-43a8-4ed4-a41e-5813c17418bb
-- title:
--   Observation 1: abort factorization
-- statement:
--   Let $P^{\rm pass}_{S_A S_B T E\mid Z}$ be a normalized classical-device law with a common finite nonempty key alphabet $\mathcal K$ and finite nonempty transcript, Eve-output and Eve-input alphabets. The $(S_A,S_B,T)$ marginal is independent of $Z$. The ideal pass law replaces the keys by a uniform perfectly correlated pair, independent of the actual $(T,E\mid Z)$ marginal. The intermediate law copies Alice's key into Bob's register and preserves $(S_A,T,E\mid Z)$. Let $r\in[0,1]$ be the abort probability, with an identical normalized abort branch in all three systems. Write $d_{\rm NS}$ for the operational NS distance, and $s,c,k$ for the pass-weighted secrecy, disagreement and security errors, respectively. Thus $s=(1-r)d_{\rm NS}(P_{S_A T E\mid Z}^{\rm pass},P_{S_A T E\mid Z}^{\rm ideal,pass})$, $c=(1-r)\Pr[S_A\ne S_B\mid\mathrm{pass}]$, and $k=(1-r)d_{\rm NS}(P^{\rm pass},P^{\rm ideal,pass})$.
--
--   Let $P^{\rm real}=rP^{\rm abort}+(1-r)P^{\rm pass}$ and $P^{\rm ideal}=rP^{\rm abort}+(1-r)P^{\rm ideal,pass}$. Then
--
--   $$d_{\rm NS}(P^{\rm real},P^{\rm ideal})=(1-r)d_{\rm NS}(P^{\rm pass},P^{\rm ideal,pass})=k.$$
--
--   A common abort branch contributes no distinguishing advantage.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 31, Observation 1 / equation (90)

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

/-- PDF p.31, Observation 1, (90): equal abort branches factor out exactly. -/
theorem abort_factorization {K T E Z : Type}
    [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    [Nonempty K] [Nonempty T] [Nonempty E] [Nonempty Z] (r : KeyOutput K T E Z) :
    cdDistance (withAbort r.abortProbability r.abort r.pass)
      (withAbort r.abortProbability r.abort (idealCDKey r.pass)) = securityError r := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
