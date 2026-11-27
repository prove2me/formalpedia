-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_Supplement_theorem2_optimal_ratio
-- name    : PersonalizedAssortment.IB.Supplement.theorem2_optimal_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:28:21.608797+00:00
-- url     : https://prove2.me/theorems/03ed90f7-f6d9-4124-98e5-ddb33631836c
-- title:
--   Theorem 2 (corrected endpoint convention), p. 1539 — exponential IB attains $1-1/e$ and no online algorithm beats $1-1/e$
-- statement:
--   Let $\Psi(x)=\frac{e}{e-1}\,(1-e^{-x})$ be the exponential penalty function. For an integer $m\ge1$, let
--   $$\alpha_m(\Psi)=\min_{x\in[0,1-1/m]}\frac{1-x}{1/m+1-\Psi(x)+\int_{x+1/m}^1\Psi(y)\,dy}$$
--   be the ratio guaranteed by Theorem 1 when $c_{\min}=m$. Then:
--
--   1. $\alpha_m(\Psi)\to1-1/e$ as $m\to\infty$;
--   2. for the asymptotic ratio,
--   $$\alpha(\Psi)=\inf_{x\in[0,1)}\frac{1-x}{1-\Psi(x)+\int_x^1\Psi(y)\,dy}=1-\frac1e;$$
--   3. no online algorithm, deterministic or randomized, has a competitive ratio better than $1-1/e$. For every $\varepsilon>0$ and every inventory level $m$ there are an instance and a horizon $T$ with the following property. The instance has $n\ge1$ products, finitely many customer types, revenues $r_i>0$, inventories $c_i\ge\max(m,1)$, a family $\mathcal S$ containing the empty assortment, and choice models satisfying Assumption 1. Every randomized online algorithm $A$ offering assortments in $\mathcal S$ then has an arrival sequence $z_1,\dots,z_T$ and a feasible solution $y$ of $\mathrm{Primal}(\{z_t\})$ with positive objective such that
--   $$\mathrm{Rev}_A(\{z_t\})\;\le\;\Big(1-\frac1e+\varepsilon\Big)\sum_t\sum_{S\in\mathcal S}\sum_i r_i\,\varphi_i^{z_t}(S)\,y^t(S).$$
--
--   Items 1–2 show that inventory balancing with the exponential penalty attains $1-1/e$ as inventories grow. Item 3 shows that no algorithm that does not know the future types can do better, even with large inventories. Together they make exponential inventory balancing optimal in the competitive-ratio sense.
--
--   **Formalization Note** Item 1 is written with the same expression as the published `PersonalizedAssortment.IB.theorem2_exponential_limit`. The competitive ratio of Definition 2 is an infimum of ratios $\mathrm{Rev}_A/\mathrm{Primal}$. Item 3 states its failure in multiplied form against a feasible LP solution, which avoids division by zero and junk infima. The endpoint convention for α is a supported boundary repair: the ratio is constant on [0,1), so the infimum is attained and agrees with extending that ratio continuously to x = 1. A randomized algorithm is a finite mixture of deterministic online policies; as explained under the definition, this covers every randomized algorithm on a finite instance.
--
--   Differences from the source:
--
--   - reading: the competitive ratio of EIB "approaches (1 − 1/e) as c_min increases to infinity" → α_m(Ψ) → 1 − 1/e as m → ∞; reason: the proof says this part "is based on Theorem 1", whose guarantee is α_{c_min}(Ψ)
--   - correction: α(Ψ) is a minimum over x ∈ [0, 1] → an infimum over x ∈ [0, 1); reason: the endpoint x = 1 is an undefined 0/0; on [0,1) the denominator equals e/(e−1) times (1−x), so the ratio is constant and its infimum is attained (e.g. at x = 0); the continuous endpoint value gives the same minimum
--   - encoding: "competitive ratio better than 1 − 1/e" (Definition 2, an infimum of Rev_A/Primal) → for every ε > 0 some sequence has Rev_A ≤ (1 − 1/e + ε)·(objective of a feasible y with positive objective); reason: the negation of inf > 1 − 1/e in multiplied form; a feasible objective is at most Primal
--   - encoding: a randomized algorithm → a finite mixture of deterministic online policies; reason: on a finite instance and horizon every distribution over deterministic policies, and by Kuhn's theorem every behavioural randomization, has the revenue of such a mixture
--   - generalization: no algorithm has a competitive ratio better than 1 − 1/e → one instance and one horizon T, given before the algorithm (which may therefore depend on T), defeat every randomized algorithm at once, and its inventories are at least any prescribed m; reason: stronger quantifier order and the large-inventory regime of the first sentence; it implies the source's claim for every algorithm
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1539, Theorem 2 (and the paragraph after it: Yao's lemma applied to Lemma 3); α_{c_min} and α from p. 1538; Definition 2, p. 1536

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_Supplement_OnlinePolicy

namespace PersonalizedAssortment.IB.Supplement

open PersonalizedAssortment.IB

/-- Theorem 2 (Exponential IB Achieves the Optimal Competitive Ratio), p. 1539, both sentences.
(a) For `Ψ(x) = (e/(e-1))(1 - e^{-x})`, `α_{c_min}(Ψ) → 1 - 1/e` as `c_min → ∞`; and
`α(Ψ) = min_x (1 - x)/(1 - Ψ(x) + ∫_x^1 Ψ(y) dy) = 1 - 1/e`, the minimum taken over `x ∈ [0, 1)`
(at `x = 1` the printed ratio is `0/0`).
(b) No online algorithm, deterministic or randomized, has a competitive ratio better than
`1 - 1/e`: for every `ε > 0` and every inventory level `m` there is an instance of the model
(`n ≥ 1` products, finitely many types, `r_i > 0`, `c_i ≥ max(m, 1)`, `∅ ∈ 𝒮`, Assumption 1) and a
horizon `T` such that every randomized online algorithm offering feasible assortments earns, on
some arrival sequence, at most `1 - 1/e + ε` times the objective of a feasible solution of
`Primal` with positive objective. -/
theorem theorem2_optimal_ratio :
    Filter.Tendsto
      (fun m : ℕ => alphaC (fun x : ℝ => Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-x))) m)
      Filter.atTop (nhds (1 - 1 / Real.exp 1)) ∧
    sInf ((fun x : ℝ => (1 - x) /
        (1 - Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-x)) +
          ∫ y in x..1, Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-y)))) '' Set.Ico 0 1) =
      1 - 1 / Real.exp 1 ∧
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      ∃ (n : ℕ) (Z : Type) (_ : Fintype Z) (r : Fin n → ℝ) (c : Fin n → ℕ)
        (𝒮 : Finset (Finset (Fin n))) (φ : Z → ChoiceModel n) (T : ℕ),
        0 < n ∧ (∀ i, 0 < r i) ∧ (∀ i, 0 < c i ∧ m ≤ c i) ∧ ∅ ∈ 𝒮 ∧ Substitutable 𝒮 φ ∧
        ∀ A : RandomizedPolicy n Z, A.IsFeasible 𝒮 →
          ∃ (z : Fin T → Z) (y : Fin T → Finset (Fin n) → ℝ),
            PrimalFeasible c 𝒮 φ z y ∧ 0 < primalObj r 𝒮 φ z y ∧
            A.revenue r c φ z ≤ (1 - 1 / Real.exp 1 + ε) * primalObj r 𝒮 φ z y := by sorry

end PersonalizedAssortment.IB.Supplement
