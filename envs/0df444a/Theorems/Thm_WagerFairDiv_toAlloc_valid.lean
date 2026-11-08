-- Prove2me | Theorems.Thm_WagerFairDiv_toAlloc_valid
-- name    : WagerFairDiv.toAlloc_valid
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:15:37.639224+00:00
-- url     : https://prove2.me/theorems/0dcee409-fb1d-4804-85c8-cc0584b5772e
-- title:
--   §3, p.4 — the allocation mechanism corresponding to a valid weakly budget-balanced wagering mechanism is valid
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal B$ be a valid wagering mechanism ($\mathcal B_{i,j}\ge0$) that is weakly budget balanced, and let $\mathcal A$ correspond to $\mathcal B$. Then $\mathcal A$ is a valid allocation mechanism: $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)\ge0$, and for all $\hat{\mathbf v}$, $\mathbf e$ and $j$,
--   $$\sum_{i=1}^n\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)=\sum_{i=1}^n\frac{\mathcal B_{i,j}(\hat{\mathbf v},\mathbf e)}{E}\le1.$$
--
--   This is the second half of the one-to-one correspondence of §3: weakly budget-balanced wagering mechanisms map into allocation mechanisms.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: B a valid wagering mechanism (Πᵢ ≥ −wᵢ, p.3) → explicit hypothesis IsWagerMech B (0 ≤ Bᵢⱼ); reason: the security form bᵢⱼ = wᵢ + Πᵢ ≥ 0 of p.3, which the paper adopts throughout; the Lean type Mech does not carry it
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), §3, p.4, "Similarly, if B is a valid weakly budget-balanced wagering mechanism, then the corresponding allocation mechanism is valid …". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), §3, p.4, "Similarly, if B is a valid weakly budget-balanced wagering mechanism":
the corresponding allocation mechanism `A` is valid, since `Aᵢ,ⱼ(v̂, e) ≥ 0` and
`Σᵢ Aᵢ,ⱼ(v̂, e) = Σᵢ Bᵢ,ⱼ(v̂, e) / E ≤ 1`. -/
theorem toAlloc_valid {n m : ℕ} (A B : Mech n m) (hB : IsWagerMech B) (hBB : WeaklyBB B)
    (hAB : Corresponding A B) : IsAllocMech A := by sorry

end WagerFairDiv
