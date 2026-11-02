-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_ccdNorm_formula
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.ccdNorm_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:01:02.793207+00:00
-- url     : https://prove2.me/theorems/2742e8c8-d48d-43ae-8ec5-4f979f8faa9b
-- title:
--   Corollary 1: cc-d formula including public transcript
-- statement:
--   Let $P^{\rm pass}_{S_A S_B T E\mid Z}$ be a normalized classical-device law with a common finite nonempty key alphabet $\mathcal K$ and finite nonempty transcript, Eve-output and Eve-input alphabets. The $(S_A,S_B,T)$ marginal is independent of $Z$. The ideal pass law replaces the keys by a uniform perfectly correlated pair, independent of the actual $(T,E\mid Z)$ marginal. The intermediate law copies Alice's key into Bob's register and preserves $(S_A,T,E\mid Z)$. Let $r\in[0,1]$ be the abort probability, with an identical normalized abort branch in all three systems. Write $d_{\rm NS}$ for the operational NS distance, and $s,c,k$ for the pass-weighted secrecy, disagreement and security errors, respectively. Thus $s=(1-r)d_{\rm NS}(P_{S_A T E\mid Z}^{\rm pass},P_{S_A T E\mid Z}^{\rm ideal,pass})$, $c=(1-r)\Pr[S_A\ne S_B\mid\mathrm{pass}]$, and $k=(1-r)d_{\rm NS}(P^{\rm pass},P^{\rm ideal,pass})$.
--
--   For any compatible cc-d states $P,Q$ on $(S_A,S_B,T,E\mid Z)$,
--
--   $$d_{\rm NS}(P,Q)=\frac12\sum_{s_A,s_B,t}\max_z\sum_e|P(s_A,s_B,t,e\mid z)-Q(s_A,s_B,t,e\mid z)|.$$
--
--   Eve may adapt her direct measurement to the entire classical tuple, including every public message.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 29, Corollary 1 / equation (79)

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

/-- PDF p.29, Corollary 1, (79): Eve can adapt to both keys and the full transcript. -/
theorem ccdNorm_formula {K T E Z : Type}
    [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    [Nonempty K] [Nonempty T] [Nonempty E] [Nonempty Z]
    (p q : CDArray (K × K × T) E Z) (hp : IsCD p) (hq : IsCD q) :
    cdDistance p q = (1 / 2 : ℝ) * ∑ a, ∑ b, ∑ t,
      finiteMax (fun z => ∑ e, |p z (a,b,t) e - q z (a,b,t) e|) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
