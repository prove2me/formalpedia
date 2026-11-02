-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_secrecy_correctness_security
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.secrecy_correctness_security
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:03:37.692394+00:00
-- url     : https://prove2.me/theorems/a08d38b6-f321-43aa-9674-c4967f5f9f46
-- title:
--   Lemma 2: secrecy plus correctness implies security
-- statement:
--   Let $P^{\rm pass}_{S_A S_B T E\mid Z}$ be a normalized classical-device law with a common finite nonempty key alphabet $\mathcal K$ and finite nonempty transcript, Eve-output and Eve-input alphabets. The $(S_A,S_B,T)$ marginal is independent of $Z$. The ideal pass law replaces the keys by a uniform perfectly correlated pair, independent of the actual $(T,E\mid Z)$ marginal. The intermediate law copies Alice's key into Bob's register and preserves $(S_A,T,E\mid Z)$. Let $r\in[0,1]$ be the abort probability, with an identical normalized abort branch in all three systems. Write $d_{\rm NS}$ for the operational NS distance, and $s,c,k$ for the pass-weighted secrecy, disagreement and security errors, respectively. Thus $s=(1-r)d_{\rm NS}(P_{S_A T E\mid Z}^{\rm pass},P_{S_A T E\mid Z}^{\rm ideal,pass})$, $c=(1-r)\Pr[S_A\ne S_B\mid\mathrm{pass}]$, and $k=(1-r)d_{\rm NS}(P^{\rm pass},P^{\rm ideal,pass})$.
--
--   For any nonnegative error budgets $\varepsilon_{\rm sec}$ and $\varepsilon_{\rm cor}$,
--
--   $$s\le\varepsilon_{\rm sec}\quad\text{and}\quad c\le\varepsilon_{\rm cor}\quad\Longrightarrow\quad k\le\varepsilon_{\rm sec}+\varepsilon_{\rm cor}.$$
--
--   Separate secrecy and correctness estimates therefore imply security.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 32, Lemma 2 / equation (105)

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

/-- PDF pp.32–33, Lemma 2, (105)–(112): the comma in (105) means subtraction,
as made explicit in (106),(112). Both error budgets are nonnegative. -/
theorem secrecy_correctness_security {K T E Z : Type}
    [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    [Nonempty K] [Nonempty T] [Nonempty E] [Nonempty Z]
    (r : KeyOutput K T E Z) (z : Z) (es ec : ℝ) (hes : 0 ≤ es) (hec : 0 ≤ ec)
    (hs : cdSecrecyError r ≤ es) (hc : correctnessError r z ≤ ec) :
    securityError r ≤ es + ec := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
