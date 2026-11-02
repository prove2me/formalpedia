-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_security_criteria
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.security_criteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:05:38.680611+00:00
-- url     : https://prove2.me/theorems/40d1ffcb-57a6-4fb9-917b-a05311e01b75
-- title:
--   Theorem 3: equivalence of NSDI security criteria
-- statement:
--   Let $P^{\rm pass}_{S_A S_B T E\mid Z}$ be a normalized classical-device law with a common finite nonempty key alphabet $\mathcal K$ and finite nonempty transcript, Eve-output and Eve-input alphabets. The $(S_A,S_B,T)$ marginal is independent of $Z$. The ideal pass law replaces the keys by a uniform perfectly correlated pair, independent of the actual $(T,E\mid Z)$ marginal. The intermediate law copies Alice's key into Bob's register and preserves $(S_A,T,E\mid Z)$. Let $r\in[0,1]$ be the abort probability, with an identical normalized abort branch in all three systems. Write $d_{\rm NS}$ for the operational NS distance, and $s,c,k$ for the pass-weighted secrecy, disagreement and security errors, respectively. Thus $s=(1-r)d_{\rm NS}(P_{S_A T E\mid Z}^{\rm pass},P_{S_A T E\mid Z}^{\rm ideal,pass})$, $c=(1-r)\Pr[S_A\ne S_B\mid\mathrm{pass}]$, and $k=(1-r)d_{\rm NS}(P^{\rm pass},P^{\rm ideal,pass})$.
--
--   The following two implications hold for all nonnegative budgets:
--
--   $$s\le\varepsilon_{\rm sec},\ c\le\varepsilon_{\rm cor}\ \Longrightarrow\ k\le\varepsilon_{\rm sec}+\varepsilon_{\rm cor},$$
--
--   $$k\le\varepsilon\ \Longrightarrow\ c\le\varepsilon\ \text{and}\ s\le\varepsilon.$$
--
--   These parameter-independent constants express the security-criterion equivalence proved by the paper.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 36, Theorem 3 / equations (148), (149)

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

/-- PDF pp.36–37, Theorem 3: the exact two implications (148),(149).
The printed arbitrary prescribed split-budget iff (147) is not asserted: it is
unjustified when one assigned budget is zero. Independent moderation is required. -/
theorem security_criteria {K T E Z : Type}
    [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    [Nonempty K] [Nonempty T] [Nonempty E] [Nonempty Z]
    (r : KeyOutput K T E Z) (z : Z) :
    (∀ es ec : ℝ, 0 ≤ es → 0 ≤ ec → cdSecrecyError r ≤ es → correctnessError r z ≤ ec →
      securityError r ≤ es + ec) ∧
    (∀ e : ℝ, 0 ≤ e → securityError r ≤ e →
      correctnessError r z ≤ e ∧ cdSecrecyError r ≤ e) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
