-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_lemma_2
-- name    : SoftenDataShare.Mutual.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:08.322751+00:00
-- url     : https://prove2.me/theorems/bd750cfa-4aba-48f0-8b78-1033003c2ae9
-- title:
--   Lemma 2 — if firm 2's uniform price also serves [z′, a], then z′ < z^N, p₂₂ < p^N_2 and firm 1 earns less than without sharing
-- statement:
--   Let $(F,f)$ be a monotone-hazard-rate distribution on $[0,1]$ and $z^N$ the benchmark marginal consumer of Eq. (1), with $p^N_2=2/h(z^N)$ and $\pi^N_1$ firm 1's benchmark profit. Consider data sharing on $[a,b]$ with
--   $$\tfrac12<a<b\le1,\qquad z^N<b,$$
--   and suppose firm 2's uniform price serves $[z',a]\cup[b,1]$, where $z'\in[0,a]$ satisfies the first-order condition (5):
--   $$z'=\frac12+\frac{1-F(b)+F(a)-F(z')}{f(z')}.$$
--   Then
--   1. $z'>1/2$;
--   2. $z'<z^N$;
--   3. firm 2's uniform price $p_{22}=2z'-1$ is below the benchmark price: $2z'-1<p^N_2$;
--   4. firm 1, which then serves $[0,z']$ at the personalized prices $p_{22}+(1-2x)$, earns strictly less than without data sharing:
--   $$\int_0^{z'}\bigl((2z'-1)+(1-2x)\bigr)\,dF(x)<\pi^N_1.$$
--
--   This is the quantitative content of Lemma 2 ("For data sharing on $[a,b]$ to be profitable for firm 1, it should necessarily induce firm 2 to choose its uniform price to serve consumers on $[b,1]$ only"): sharing that leads firm 2 to compete for $[z',a]$ lowers its uniform price and hurts firm 1. It is the reason firm 2's incentive constraint (IC) $\pi_{21}(b)\ge\pi_{22}(a,b)$ appears in firm 1's problem.
--
--   **Formalization Note** The paper's claim $z'>1/2$ in (5) is part of the conclusion, not a hypothesis; the hypothesis on $z'$ is only $0\le z'\le a$.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 10, Lemma 2 and Eq. (5); proof p. 34

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem lemma_2 {F f : ℝ → ℝ} {zN a b z' : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) (ha : 1 / 2 < a) (hab : a < b) (hb : b ≤ 1) (hzNb : zN < b)
    (hz' : z' ∈ Set.Icc 0 a)
    (hfoc : z' = 1 / 2 + (1 - F b + F a - F z') / f z') :
    1 / 2 < z' ∧ z' < zN ∧ 2 * z' - 1 < pN2 F f zN ∧
      (∫ x in (0 : ℝ)..z', ((2 * z' - 1) + (1 - 2 * x)) * f x) < piN1 F f zN := by sorry

end SoftenDataShare.Mutual
