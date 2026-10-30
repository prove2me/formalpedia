-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_proposition_4
-- name    : RepeatedNRM.Myopic.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:52.441009+00:00
-- url     : https://prove2.me/theorems/c31f99bf-c8a0-47e3-b6ba-ac0b95d1b0a2
-- title:
--   Proposition 4, p. 22 — dynamic complementary slackness: under-spent budgets have zero dual price next period
-- statement:
--   Assume every $\varphi_j$ satisfies Assumption 1 and Assumption 2 holds with $\gamma=0$. Let $x^{MY}_1$ be a myopic allocation at budgets $\mathbf b_1\in[0,1]^m$ and $\mathbf b_2=\boldsymbol\varphi(\mathbf b_1,\mathbf q(\mathbf b_1,x^{MY}_1))$ the updated budgets. Consider the dual of the myopic linear program (7) at $\mathbf b_2$:
--   $$\min_{\mu,\lambda\ge 0}\ \sum_i s_i\lambda_i+\sum_j b_{j,2}\mu_j\quad\text{s.t.}\quad \lambda_i+p_{ij}\mu_j\ge p_{ij}\ \ \forall i,j.$$
--   Then there is a dual optimal solution $(\mu_2,\lambda_2)$ such that
--   $$\mu_{j,2}=0\qquad\text{for every customer } j \text{ with } \sum_{i\in A_j}p_{ij}x^{MY}_{ij,1}<b_{j,1}.$$
--
--   If the myopic policy leaves part of a customer's budget unspent, a larger budget for that customer next period has no marginal value. This "dynamic complementary slackness" is the key to Theorem 2.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - reading: "the myopic policy" $\{\mathbf x^{MY}_t\}$ → every trajectory whose allocation in each period is an optimal solution of (7) at the current budgets; reason: (7) can have several optimal solutions; the statement is made for every selection, the stronger of the two readings
--   - reading: "if $\sum_{i\in A_j}p_{ij}x^{MY}_{ij,1}<b_{j,1}$ there exists a dual optimal solution … such that $\mu_{j,2}=0$ for each customer $j$" → one dual optimal solution with $\mu_{j,2}=0$ simultaneously for every under-spending customer $j$; reason: the sentence admits a per-customer and a simultaneous reading; the simultaneous one is stronger and is what the proof of Theorem 2 uses when it raises all such budgets at once
--   - encoding: a dual optimal solution "associated to $x^{MY}_2$", a myopic allocation at $\mathbf b_2$ → a dual optimal solution of (7) at $\mathbf b_2$; $x^{MY}_2$ is not a parameter; reason: by LP duality every dual optimal solution satisfies complementary slackness with every primal optimal one, and a primal optimum exists, so the phrase adds no condition
--   - generalization: service quality (3): $q_j = U_j/U^*_j$ if $b_j>0$, $q_j = 1$ if $b_j = 0$ (undefined when $U^*_j(b_j)=0<b_j$) → $q_j = 1$ if $b_j = 0$ or $U^*_j(b_j) = 0$, else $U_j/U^*_j$; reason: (3) divides by $U^*_j(b_j)$, which is $0$ for $b_j>0$ exactly when no desired product has positive surplus or supply; Lean also covers these instances, where the paper's model is undefined, and agrees with (3) wherever (3) is defined
--   - encoding: Assumption 2(i), which divides by $p_{ij}$ for $i\in A_j$ → Assumption 2 includes $p_{ij}>0$ for $i\in A_j$; reason: the ratios $v_{ij}/p_{ij}$ are undefined otherwise; this excludes only undefined cases
--   - encoding: $\min_{i\in A_j} v_{ij}/p_{ij} - 1 \ge (1-\gamma)(\max_{i\in A_j} v_{ij}/p_{ij} - 1)$ → $v_{ij}/p_{ij} - 1 \ge (1-\gamma)(v_{kj}/p_{kj} - 1)$ for all $i,k\in A_j$; reason: equivalent for nonempty $A_j$; for empty $A_j$ the min and max are undefined and the pairwise clause is vacuous
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. 22, Proposition 4 (restated p. ec2; dual of (7) on p. ec2)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Proof

namespace RepeatedNRM.Myopic

theorem proposition_4 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (h1 : ∀ j, Assumption1i I j ∧ Assumption1ii I j ∧ Assumption1iii I j)
    (h2 : Assumption2 I A 0) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (x1 : Fin I.n → Fin I.m → ℝ) (hx1 : IsMyopicAlloc I b1 x1) :
    ∃ (μ : Fin I.m → ℝ) (lam : Fin I.n → ℝ), DualOptimal I (update I b1 x1) μ lam ∧
      ∀ j, ∑ i ∈ A j, I.p i j * x1 i j < b1 j → μ j = 0 := by sorry
end RepeatedNRM.Myopic
