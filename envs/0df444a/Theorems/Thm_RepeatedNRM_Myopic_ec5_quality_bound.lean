-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_ec5_quality_bound
-- name    : RepeatedNRM.Myopic.ec5_quality_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:04.684036+00:00
-- url     : https://prove2.me/theorems/82a490e2-bb9f-4f1a-969e-a7e13589fdc9
-- title:
--   (EC.5), p. ec7 (corrected: feasible allocations only) — service quality ≥ (1 − γ) × fill rate
-- statement:
--   Assume Assumption 2 holds with characteristic sets $A_j$ and parameter $\gamma\in[0,1]$. For every customer $j$, budget $b_j\in[0,1]$ and allocation $x_j\in X_j(b_j)$ (so $0\le x_{ij}\le s_i$ and $\sum_i p_{ij}x_{ij}\le b_j$), the service quality is bounded below by $1-\gamma$ times the fill rate:
--   $$q_j(b_j,x_j)\ \ge\ (1-\gamma)\cdot\frac{\sum_{i\in A_j}p_{ij}x_{ij}}{\min\bigl(b_j,\ \sum_{i\in A_j}p_{ij}s_i\bigr)}.$$
--
--   The quality perceived by a customer is controlled by the fraction of its attainable spending that is served. The bound reduces the general case to the $\gamma=0$ analysis, scaled by $1-\gamma$.
--
--   Differences from the source:
--   - correction: "for any budget $b_j$ and allocation $x_j$" → $x_j\in X_j(b_j)$; reason: for $x_j\notin X_j(b_j)$ the paper sets $U_j=0$ (p. 10), so $q_j=0$ while the right-hand side is positive, e.g. a single product with $p=1$, $v=2$, $s=1$, $b_j=1/2$ and $x_j=1$ gives $0\ge(1-\gamma)\cdot 2$, false for $\gamma<1$
--   - encoding: the chain $q_j=\dots\ge\dots\ge(1-\gamma)\cdot$ fill rate, whose middle term uses an optimal $y^*(b_j)$ → only the outer inequality; reason: the middle term is a step of the derivation; the displayed conclusion is the outer inequality
--   - encoding: the fill rate when $\min(b_j,\sum_{i\in A_j}p_{ij}s_i)=0$ (undefined) → the left side is $0$ (Lean's $a/0=0$); reason: there the quality is $1$, so the bound holds trivially; no defined instance changes
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - generalization: service quality (3): $q_j = U_j/U^*_j$ if $b_j>0$, $q_j = 1$ if $b_j = 0$ (undefined when $U^*_j(b_j)=0<b_j$) → $q_j = 1$ if $b_j = 0$ or $U^*_j(b_j) = 0$, else $U_j/U^*_j$; reason: (3) divides by $U^*_j(b_j)$, which is $0$ for $b_j>0$ exactly when no desired product has positive surplus or supply; Lean also covers these instances, where the paper's model is undefined, and agrees with (3) wherever (3) is defined
--   - encoding: Assumption 2(i), which divides by $p_{ij}$ for $i\in A_j$ → Assumption 2 includes $p_{ij}>0$ for $i\in A_j$; reason: the ratios $v_{ij}/p_{ij}$ are undefined otherwise; this excludes only undefined cases
--   - encoding: $\min_{i\in A_j} v_{ij}/p_{ij} - 1 \ge (1-\gamma)(\max_{i\in A_j} v_{ij}/p_{ij} - 1)$ → $v_{ij}/p_{ij} - 1 \ge (1-\gamma)(v_{kj}/p_{kj} - 1)$ for all $i,k\in A_j$; reason: equivalent for nonempty $A_j$; for empty $A_j$ the min and max are undefined and the pairwise clause is vacuous
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. ec7, EC.2.2, inequality (EC.5)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem ec5_quality_bound (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (γ : ℝ) (h2 : Assumption2 I A γ) (j : Fin I.m) (bj : ℝ) (hbj : bj ∈ Set.Icc (0 : ℝ) 1)
    (y : Fin I.n → ℝ) (hy : custFeasible I j bj y) :
    (1 - γ) * ((∑ i ∈ A j, I.p i j * y i) / min bj (∑ i ∈ A j, I.p i j * I.s i)) ≤
      quality I j bj y := by sorry
end RepeatedNRM.Myopic
