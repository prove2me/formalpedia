-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_lemma_3
-- name    : RepeatedNRM.Myopic.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:04.776851+00:00
-- url     : https://prove2.me/theorems/2014a2f1-832a-4077-9bf7-2c2a5a6f7fe2
-- title:
--   Lemma 3, p. ec4 — at γ = 0 the myopic allocation remains budget-feasible after the update
-- statement:
--   Let $x^{MY}_1$ be a myopic allocation at budgets $\mathbf b_1\in[0,1]^m$ and let $\mathbf b_2=\boldsymbol\varphi(\mathbf b_1,\mathbf q(\mathbf b_1,x^{MY}_1))$ be the updated budgets. Assume every $\varphi_j$ satisfies Assumption 1 and that Assumption 2 holds with $\gamma=0$, so that every customer has the same bang-per-buck ratio on all its desired products. Then $x^{MY}_1\in X(\mathbf b_2)$, i.e.
--   $$\sum_{i\in A_l}p_{il}x^{MY}_{il,1}\le b_{l,2}\qquad\text{for each customer } l.$$
--
--   A customer's spending never exceeds next period's budget under the myopic policy. This is the step that fails once $\gamma>0$.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - reading: "the myopic policy" $\{\mathbf x^{MY}_t\}$ → every trajectory whose allocation in each period is an optimal solution of (7) at the current budgets; reason: (7) can have several optimal solutions; the statement is made for every selection, the stronger of the two readings
--   - generalization: service quality (3): $q_j = U_j/U^*_j$ if $b_j>0$, $q_j = 1$ if $b_j = 0$ (undefined when $U^*_j(b_j)=0<b_j$) → $q_j = 1$ if $b_j = 0$ or $U^*_j(b_j) = 0$, else $U_j/U^*_j$; reason: (3) divides by $U^*_j(b_j)$, which is $0$ for $b_j>0$ exactly when no desired product has positive surplus or supply; Lean also covers these instances, where the paper's model is undefined, and agrees with (3) wherever (3) is defined
--   - encoding: Assumption 2(i), which divides by $p_{ij}$ for $i\in A_j$ → Assumption 2 includes $p_{ij}>0$ for $i\in A_j$; reason: the ratios $v_{ij}/p_{ij}$ are undefined otherwise; this excludes only undefined cases
--   - encoding: $\min_{i\in A_j} v_{ij}/p_{ij} - 1 \ge (1-\gamma)(\max_{i\in A_j} v_{ij}/p_{ij} - 1)$ → $v_{ij}/p_{ij} - 1 \ge (1-\gamma)(v_{kj}/p_{kj} - 1)$ for all $i,k\in A_j$; reason: equivalent for nonempty $A_j$; for empty $A_j$ the min and max are undefined and the pairwise clause is vacuous
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. ec4, Lemma 3, (EC.1)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem lemma_3 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (h1 : ∀ j, Assumption1i I j ∧ Assumption1ii I j ∧ Assumption1iii I j)
    (h2 : Assumption2 I A 0) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin I.n → Fin I.m → ℝ) (hx : IsMyopicAlloc I b1 x) :
    feasible I (update I b1 x) x := by sorry
end RepeatedNRM.Myopic
