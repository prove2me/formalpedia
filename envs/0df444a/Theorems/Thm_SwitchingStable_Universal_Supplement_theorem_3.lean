-- Prove2me | Theorems.Thm_SwitchingStable_Universal_Supplement_theorem_3
-- name    : SwitchingStable.Universal.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:39:03.342302+00:00
-- url     : https://prove2.me/theorems/c2a19c8b-1660-4fc5-8425-7f54bb1cdcc4
-- title:
--   Theorem 3 — both side costs, finite lists and arbitrary private subsets
-- statement:
--   Let $I$ be any complete strict market of size $n$, $N=|\operatorname{Stab}(I)|$, and $S\in\{U,V\}$ either side. The stable-partner degrees are $d_a$. Use every stable matching, all exact stable-edge witnesses, and independent uniform reveal priorities in the side cost $K_S$. Then
--
--   $$N\le\exp(\min\{K_U,K_V\}),\qquad K_S\le\sum_{a\in S}c_{d_a}.$$
--
--   For every integer $r\ge1$ and every fixed subset $A\subseteq S$ whose disjoint $r$-private pools exist for every stable matching and every $a\in A$,
--
--   $$K_S\le |A|C_r+(n-|A|)C.$$
--
--   There is no private-pool assumption in the first two inequalities. In the private clause the pools are disjoint only over boundaries for a fixed agent and matching, with no reveal-dependent choices. For positive $n$, the count obeys the explicit combination
--
--   $$N\le\min\!\left\{\Omega^n,\ \exp\!\left(\min\left\{\sum_{a\in S}c_{d_a},\ |A|C_r+(n-|A|)C\right\}\right)\right\}.$$
--
--   More generally, any simultaneous upper estimates $K_U\le b_U$ and $K_V\le b_V$ give $N\le\min\{\Omega^n,\exp(\min\{b_U,b_V\})\}$. Here $\Omega$ is the already published goal's explicit universal base. Its definition is reused without a new constant or a new universal-goal item.
--
--   The statement includes the setting and proof's well-posedness facts: every market has a nonempty stable set; its index encoding is injective; its exact certificate system is valid and agrees with the fixed-edge witness definition; every actual interval has length at least one; and the logarithmic random sums are integrable. Every market is $1$-private on its whole side. Any valid witness-subset family gives a cost at least $K_S$ and still bounds $N$ after exponentiation. If it retains all canonical witnesses, its cost also satisfies the finite-list estimate. Its expectation is integrable as well.
--
--   The complete private series is summable for every $r\ge1$, the positive-parameter geometric logarithm series is summable, and
--
--   $$C_r=\int_0^1\mathbb E\log(G_{1-(1-x)^r}+G'_{1-(1-x)^r}-1)\,dx,\quad C_1=C,\quad C_2=C_{2,\mathrm{published}}.$$
--
--   The integrand is integrable, $C_{r+1}<C_r$ for $r\ge1$, and $C_r\to0$. The geometric variables are independent and positive-integer valued. These evaluations are companion instance-sensitive bounds; they impose no promoted-list condition on $I$.
--
--   Differences from the source:
--   - encoding: uniform stable matching and independent uniform priorities on either side → finite uniform sum divided by numStable, published revealLaw, and side reversal; reason: all stable matchings and both complete rank families are preserved
--   - encoding: well-defined finite certificate costs and convergent C_r representation in the setting and proof → nonempty stable family, injectivity, validity, positive lengths, integrability and summability are conclusions; reason: none is assumed as an input, and no total-function default supplies a bound
--   - encoding: smallest applicable estimate and universal estimate may be used together → explicit minima of finite-list, private and universal bounds and a quantified upper-estimate combination clause; reason: all applicable bounds concern the same cost; the universal bound is the immutable goal reference
--   - encoding: private geometric integrand on x in (0,1] → the private integrand is zero at x=0; C_1=C, C_2=C2, strict decrease and limit zero are included; reason: a single null endpoint changes no integral, and the full proof conclusions are retained
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 37, PDF p. 38, Theorem 3; Section 6 and Appendices G–I

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Supplement_StableCertificates
import Definitions.Def_SwitchingStable_Universal_Supplement_Costs

namespace SwitchingStable.Universal.Supplement

open StableMatching MeasureTheory Filter

theorem theorem_3 {n : ℕ} (I : Instance n) :
    (StableCount.numStable I : ℝ) ≤ Real.exp (min (sideCost I .U) (sideCost I .V)) ∧
    (∀ s : Side, sideCost I s ≤ ∑ u : Fin n, finiteCost (degree (onSide I s) u)) ∧
    (∀ (s : Side) (r : ℕ) (A : Finset (Fin n)), 1 ≤ r → PrivateOn (onSide I s) A r →
      sideCost I s ≤ (A.card : ℝ) * privateCost r + (n - A.card : ℕ) * C) ∧
    (∀ (s : Side) (r : ℕ) (A : Finset (Fin n)), 1 ≤ n → 1 ≤ r →
      PrivateOn (onSide I s) A r →
      (StableCount.numStable I : ℝ) ≤ min (Omega ^ n)
        (Real.exp (min (∑ u : Fin n, finiteCost (degree (onSide I s) u))
          ((A.card : ℝ) * privateCost r + (n - A.card : ℕ) * C)))) ∧
    (∀ bU bV : ℝ, 1 ≤ n → sideCost I .U ≤ bU → sideCost I .V ≤ bV →
      (StableCount.numStable I : ℝ) ≤ min (Omega ^ n) (Real.exp (min bU bV))) ∧
    (∀ s : Side, 0 < StableCount.numStable (onSide I s) ∧
      (stableCertificate (onSide I s)).Valid ∧
      Function.Injective (fun μ : StableSet (onSide I s) => indexVector (onSide I s) μ.val) ∧
      PrivateOn (onSide I s) Finset.univ 1 ∧
      ∀ μ : Matching n, (onSide I s).IsStable μ →
        (∀ u j, 1 ≤ j → j < degree (onSide I s) u →
          (stableCertificate (onSide I s)).witnesses (indexVector (onSide I s) μ) u j =
            exactWitness (onSide I s) μ u j) ∧
        (∀ u (P : Finset (Fin n)),
          1 ≤ (stableCertificate (onSide I s)).length (indexVector (onSide I s) μ) u P) ∧
        Integrable (logLengthSum (stableCertificate (onSide I s))
          (indexVector (onSide I s) μ)) (revealLaw n)) ∧
    (∀ (s : Side) (H : WitnessFamily n), IsSubsetFamily (onSide I s) H →
      (∀ μ : Matching n, (onSide I s).IsStable μ →
        Integrable (logLengthSum (withWitnesses (onSide I s) H)
          (indexVector (onSide I s) μ)) (revealLaw n)) ∧
      sideCost I s ≤ certificateCost (onSide I s) (withWitnesses (onSide I s) H) ∧
      (StableCount.numStable I : ℝ) ≤
        Real.exp (certificateCost (onSide I s) (withWitnesses (onSide I s) H)) ∧
      (ContainsCanonical (onSide I s) H →
        certificateCost (onSide I s) (withWitnesses (onSide I s) H) ≤
          ∑ u : Fin n, finiteCost (degree (onSide I s) u))) ∧
    (∀ y : ℝ, 0 < y → y ≤ 1 → Summable (geometricTerm y)) ∧
    (∀ r : ℕ, 1 ≤ r → Summable (privateSeriesTerm r) ∧
      Integrable (privateIntegrand r) unitLaw ∧
      privateCost r = ∫ x, privateIntegrand r x ∂unitLaw) ∧
    privateCost 1 = C ∧ privateCost 2 = C2 ∧
    (∀ r : ℕ, 1 ≤ r → privateCost (r + 1) < privateCost r) ∧
    Tendsto privateCost atTop (nhds 0) := by sorry

end SwitchingStable.Universal.Supplement
