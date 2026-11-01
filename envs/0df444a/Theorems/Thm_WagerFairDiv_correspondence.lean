-- Prove2me | Theorems.Thm_WagerFairDiv_correspondence
-- name    : WagerFairDiv.correspondence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:53.292903+00:00
-- url     : https://prove2.me/theorems/afc0d8c7-c71a-46ec-a925-82454f4930a0
-- title:
--   The correspondence (§3, pp.4–5; corrected Theorem 3): allocation mechanisms are exactly weakly budget-balanced wagering mechanisms, with IC, proportionality ⇔ IR and Pareto optimality transferred
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   For all $n$ and $m$:
--
--   1. **Bijection** (§3, p.4). If $\mathcal A$ is a valid allocation mechanism, $W\mathcal A$ is a valid, weakly budget-balanced wagering mechanism. If $\mathcal B$ is a valid, weakly budget-balanced wagering mechanism, $\mathcal B/E$ is a valid allocation mechanism. The maps $\mathcal A\mapsto W\mathcal A$ and $\mathcal B\mapsto\mathcal B/E$ are inverse to each other, and $\mathcal B=W\mathcal A$ holds if and only if $\mathcal A=\mathcal B/E$ (the two forms of Definition 10).
--   2. **Theorem 1** (p.5). For corresponding $\mathcal A$, $\mathcal B$: $\mathcal A$ is weakly (resp. strictly) incentive compatible iff $\mathcal B$ is.
--   3. **Theorem 2** (p.5). For corresponding $\mathcal A$, $\mathcal B$ with $\mathcal A$ weakly incentive compatible: $\mathcal A$ is proportional iff $\mathcal B$ is individually rational.
--   4. **Theorem 3, corrected** (p.5). For a valid allocation mechanism $\mathcal A$ and its corresponding $\mathcal B$:
--   $$\mathcal A\text{ Pareto optimal}\iff\mathcal B\text{ side-bet Pareto optimal and }\textstyle\sum_i\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\text{ whenever some }\hat p_{k,j}>0.$$
--
--   This is the paper's headline: "there is a one-to-one correspondence between weakly budget-balanced wagering mechanisms and allocation mechanisms for divisible goods" (§3, p.4), under which incentive compatibility, proportionality / individual rationality and the two Pareto notions match.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: the profile (vᵢ, v̂₋ᵢ), resp. (pᵢ, p̂₋ᵢ) → Function.update v̂ i vᵢ; reason: the same profile
--   - encoding: strictly incentive compatible: "this inequality is strict whenever vᵢ ≠ v̂ᵢ" (Definitions 4, 7) → weak IC together with the strict inequality for every report vᵢ ≠ v̂ᵢ; reason: at vᵢ = v̂ᵢ both sides coincide, so the conjunction holds for exactly the same mechanisms
--   - encoding: IR: there is a report p̂ᵢ such that for all p̂₋ᵢ and w … (Definition 5) → ∃ r, ∀ p̂ w, with agent i's entry of p̂ replaced by r (Function.update); reason: quantifying over full profiles and overwriting entry i is the same as quantifying over p̂₋ᵢ; r depends on i and pᵢ only, as printed
--   - reading: "random assignment mechanism" (Theorems 1–3, p.5) → an allocation mechanism of §2.1 (a Mech; validity IsAllocMech where needed); reason: the term is never defined in the paper and is a leftover name for the allocation mechanisms of §2.1, which Definition 10 pairs with wagering mechanisms
--   - encoding: Theorem 2: "A (weakly) incentive compatible … corresponding (weakly) incentive compatible B" → clause 3 assumes only AllocWeakIC A; reason: equivalent to weak IC of B for corresponding mechanisms (clause 2), so the same pairs are covered
--   - encoding: A "outputs a feasible allocation" (standing assumption of §2.1, p.2) → explicit hypothesis IsAllocMech A; reason: the paper's definition of an allocation mechanism; the Lean type Mech does not carry it
--   - reading: Pareto optimality over "all alternative allocations" (Definition 3) → alternatives a′ range over feasible allocations (a′ᵢⱼ ≥ 0, Σᵢ a′ᵢⱼ ≤ 1); reason: §2.1, p.2 defines allocations as feasible ones; over infeasible alternatives no mechanism would be Pareto optimal
--   - encoding: Definition 8, condition 2: minⱼ (bᵢⱼ + Δbᵢⱼ) ≥ 0 → 0 ≤ bᵢⱼ + Δbᵢⱼ for all i, j; reason: equivalent for m ≥ 1; for m = 0 there are no profiles, since the simplex over Fin 0 is empty
--   - correction: A Pareto optimal iff B side-bet Pareto optimal and strictly budget balanced (Σᵢ Bᵢⱼ = W for every j) → A Pareto optimal iff B side-bet Pareto optimal and BBOnSupport B (Σᵢ Bᵢⱼ(p̂, w) = W for every j with p̂ₖⱼ > 0 for some k); reason: the printed "only if" is false: n = 1, m = 2, A₁ⱼ(v̂, e) = 1 if v̂₁ⱼ > 0 else 0 is feasible and Pareto optimal (agent 1 gets value 1, the maximum), yet at v̂₁ = (1, 0) Σᵢ Bᵢ,₂ = 0 < W; strict budget balance implies BBOnSupport, so the printed "if" direction follows from the corrected one
--   - encoding: B a valid wagering mechanism (Πᵢ ≥ −wᵢ, p.3) → explicit hypothesis IsWagerMech B (0 ≤ Bᵢⱼ); reason: the security form bᵢⱼ = wᵢ + Πᵢ ≥ 0 of p.3, which the paper adopts throughout; the Lean type Mech does not carry it
--   - generalization: Theorems 1 and 2, the mutual inverse property and the two forms of Definition 10 concern valid allocation and wagering mechanisms → clauses 2 and 3 and the last three conjuncts of clause 1 hold for arbitrary elements of Mech, with no IsAllocMech or IsWagerMech hypothesis; reason: those arguments use only the correspondence and W > 0 (or E > 0); adding the validity hypotheses recovers the printed statements
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), §3 The Correspondence, pp.4–5: Definition 10 and its validity paragraphs (p.4), Theorems 1, 2, 3 (p.5); proofs in Appendix A, pp.12–14. PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- **The correspondence** — Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), §3, pp.4–5: Definition 10 with its validity paragraphs
(p.4) and Theorems 1, 2, 3 (p.5).

1. (p.4) `A ↦ W·A` maps allocation mechanisms into weakly budget-balanced wagering mechanisms,
   `B ↦ B/E` maps weakly budget-balanced wagering mechanisms into allocation mechanisms, the two
   maps are mutually inverse, and the two forms of Definition 10 are equivalent.
2. (Theorem 1) For corresponding `A`, `B`: `A` is weakly (strictly) IC iff `B` is.
3. (Theorem 2) For corresponding `A`, `B` with `A` weakly IC: `A` proportional iff `B`
   individually rational.
4. (Theorem 3, **corrected**) For a valid `A` corresponding to `B`: `A` Pareto optimal iff `B`
   side-bet Pareto optimal and budget balanced on every outcome some agent reports possible.

**Formalization Note.** Agents `Fin n`, goods/outcomes `Fin m` (0-based); reports in
`stdSimplex ℝ (Fin m)`; weights / wagers strictly positive. The printed Theorem 3 requires strict
budget balance, whose "only if" is false (n = 1, m = 2; see `theorem_3`). -/
theorem correspondence (n m : ℕ) :
    ((∀ A : Mech n m, IsAllocMech A → IsWagerMech (toWager A) ∧ WeaklyBB (toWager A)) ∧
      (∀ B : Mech n m, IsWagerMech B → WeaklyBB B → IsAllocMech (toAlloc B)) ∧
      (∀ A : Mech n m, toAlloc (toWager A) = A) ∧
      (∀ B : Mech n m, toWager (toAlloc B) = B) ∧
      (∀ A B : Mech n m, Corresponding A B ↔
        ∀ (v : Profile n m) (e : PosVec n) (i : Fin n) (j : Fin m),
          A v e i j = B v e i j / e.total)) ∧
    (∀ A B : Mech n m, Corresponding A B →
      (AllocWeakIC A ↔ WagerWeakIC B) ∧ (AllocStrictIC A ↔ WagerStrictIC B)) ∧
    (∀ A B : Mech n m, Corresponding A B → AllocWeakIC A →
      (Proportional A ↔ IndivRational B)) ∧
    (∀ A B : Mech n m, IsAllocMech A → Corresponding A B →
      (ParetoOptimal A ↔ SideBetPO B ∧ BBOnSupport B)) := by sorry

end WagerFairDiv
