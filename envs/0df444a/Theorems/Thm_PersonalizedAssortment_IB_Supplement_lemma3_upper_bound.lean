-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_Supplement_lemma3_upper_bound
-- name    : PersonalizedAssortment.IB.Supplement.lemma3_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:27:45.040567+00:00
-- url     : https://prove2.me/theorems/96680487-4a26-4f74-8050-77e319b0d6b5
-- title:
--   Lemma 3, p. 1538 — on the phase construction every deterministic online algorithm earns at most $\rho_n\cdot\mathrm{Primal}$ on some sequence
-- statement:
--   Let $n\ge1$ and $k\ge1$. Consider the instance of the proof of Lemma 3 (p. 1539). It has $n$ products with revenue $r_i=1$ and initial inventory $c_i=k$, every assortment is feasible, and the horizon is $T=nk$. Its customer types are sets $\Theta$ of equally liked products with the choice model $\varphi_i^\Theta(S)=1/|S\cap\Theta|$ for $i\in S\cap\Theta$. The arrival sequences are the $n!$ phase sequences $z^\sigma$: in phase $j=0,\dots,n-1$, the $k$ customers have type $\{\sigma(j),\dots,\sigma(n-1)\}$. Let
--   $$\rho_n=\frac1n\sum_{j=1}^n\min\Big\{\sum_{t=1}^j\frac{1}{n-t+1},\,1\Big\}.$$
--   Then:
--
--   1. the construction satisfies Assumption 1 (substitutability);
--   2. for every deterministic online algorithm $\pi$ there are a permutation $\sigma$ and a feasible solution $y$ of $\mathrm{Primal}(z^\sigma)$ with positive objective such that
--   $$\mathrm{Rev}_\pi(z^\sigma)\;\le\;\rho_n\cdot\sum_{t}\sum_{S}\sum_i r_i\,\varphi_i^{z^\sigma_t}(S)\,y^t(S).$$
--
--   Since the objective of a feasible $y$ is at most $\mathrm{Primal}(z^\sigma)$, the revenue of $\pi$ on $z^\sigma$ is at most a fraction $\rho_n$ of $\mathrm{Primal}(z^\sigma)$. The algorithm may depend on $n$, $k$ and the distribution of $\sigma$, which covers the optimal dynamic program.
--
--   This is the deterministic upper bound on the competitive ratio. With Yao's principle it gives the impossibility half of Theorem 2, because $\rho_n\to1-1/e$.
--
--   **Formalization Note** The paper writes the inventories as $T/n$ with $T$ a multiple of $n$; here the phase length $k$ is the parameter and $T=nk$. The bound is claimed for every $k\ge1$; no limit in $T$ is taken. The stochastic process is the uniform distribution over the sequences $z^\sigma$, and "there exists a sequence" is the existence of $\sigma$.
--
--   Differences from the source:
--
--   - encoding: products and periods numbered from 1, inventories T/n with T a multiple of n → indices from 0, phase length k with c_i = k and T = n k; reason: the same instances
--   - encoding: the bound is stated against the LP optimum Primal({z_t}) → against the objective of a feasible y with positive objective; reason: a feasible objective is at most Primal, so the Lean bound implies the source's; the LP optimum is attained, so the two are equivalent
--   - generalization: a deterministic algorithm that does not know the future types → an OnlinePolicy that sees the past and current types and the past outcomes, stocked-out picks included; reason: the information structure of §A.2, p. 1548; extra observations only enlarge the class of algorithms bounded
--   - reading: the feasible family 𝒮 of the construction is not stated → every subset of products is feasible; reason: the largest family is the most favourable to the algorithm and contains the empty offer
--   - encoding: 2^n − 1 nonempty types → the type space is all finite sets of products, the empty set never arriving; reason: a type that never arrives changes no instance
--   - generalization: the construction is "a special case of the multinomial logit choice model" (p. 1539) → Lean also asserts that it satisfies Assumption 1; reason: an added conclusion clause; dropping it gives the source claim
--   - generalization: the construction asks that T be very large (and a multiple of n) → the exact bound holds for every integer phase length k ≥ 1; reason: uniformity in finite phase length strengthens the asymptotic presentation; it includes arbitrarily large T = n k
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1538, Lemma 3; construction p. 1539

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_Supplement_OnlinePolicy
import Definitions.Def_PersonalizedAssortment_IB_Supplement_PhaseInstance

namespace PersonalizedAssortment.IB.Supplement

open PersonalizedAssortment.IB

/-- Lemma 3 (Upper Bound on the Competitive Ratio), p. 1538, on the construction of p. 1539: `n`
products with unit revenues, initial inventories `k` each, horizon `T = n k`, customer types the
sets `Θ` of equally liked products (`phaseChoice`), every assortment feasible, and the arrival
sequences `z^σ` (`phaseSeq k σ`) for the `n!` permutations `σ`. The construction satisfies
Assumption 1, and for every deterministic online policy there is a permutation `σ` and a feasible
solution `y` of `Primal(z^σ)` with positive objective such that the policy's expected revenue on
`z^σ` is at most `ρ_n` times the objective of `y`. -/
theorem lemma3_upper_bound (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Substitutable (Finset.univ : Finset (Finset (Fin n))) (phaseChoice (n := n)) ∧
    ∀ π : OnlinePolicy n (Finset (Fin n)),
      ∃ σ : Equiv.Perm (Fin n), ∃ y : Fin (n * k) → Finset (Fin n) → ℝ,
        PrimalFeasible (fun _ => k) Finset.univ phaseChoice (phaseSeq k σ) y ∧
        0 < primalObj (fun _ => 1) Finset.univ phaseChoice (phaseSeq k σ) y ∧
        policyRevenue (fun _ => 1) (fun _ => k) phaseChoice π (phaseSeq k σ) ≤
          rhoN n * primalObj (fun _ => 1) Finset.univ phaseChoice (phaseSeq k σ) y := by sorry

end PersonalizedAssortment.IB.Supplement
