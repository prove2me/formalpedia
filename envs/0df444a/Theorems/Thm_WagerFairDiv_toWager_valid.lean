-- Prove2me | Theorems.Thm_WagerFairDiv_toWager_valid
-- name    : WagerFairDiv.toWager_valid
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:35.622991+00:00
-- url     : https://prove2.me/theorems/84821d2a-1c37-41e8-b283-460307f6d031
-- title:
--   §3, p.4 — the wagering mechanism corresponding to a valid allocation mechanism is valid and weakly budget balanced
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ be a (valid) allocation mechanism, i.e. it outputs a feasible allocation on every input, and let $\mathcal B$ correspond to $\mathcal A$. Then $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)\ge0$ for all inputs, $i$, $j$, and for all $\hat{\mathbf p}$, $\mathbf w$ and $j$,
--   $$\sum_{i=1}^n\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=\sum_{i=1}^n W\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)\le W.$$
--   So $\mathcal B$ is a valid, weakly budget-balanced wagering mechanism.
--
--   This is the first half of the one-to-one correspondence of §3: allocation mechanisms map into weakly budget-balanced wagering mechanisms.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: A "outputs a feasible allocation" (standing assumption of §2.1, p.2) → explicit hypothesis IsAllocMech A; reason: the paper's definition of an allocation mechanism; the Lean type Mech does not carry it
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), §3, p.4, "If A is a valid allocation mechanism, then its corresponding wagering mechanism satisfies … It is therefore a well-defined, weakly budget-balanced wagering mechanism.". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), §3, p.4, "It is therefore a well-defined, weakly budget-balanced wagering
mechanism": if `A` is a valid allocation mechanism, its corresponding wagering mechanism `B`
satisfies `Bᵢ,ⱼ(p̂, w) ≥ 0` and `Σᵢ Bᵢ,ⱼ(p̂, w) = Σᵢ W Aᵢ,ⱼ(p̂, w) ≤ W`. -/
theorem toWager_valid {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A)
    (hAB : Corresponding A B) : IsWagerMech B ∧ WeaklyBB B := by sorry

end WagerFairDiv
