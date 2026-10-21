-- Prove2me | Theorems.Thm_RawBlending_UB_theorem_1_production
-- name    : RawBlending.UB.theorem_1_production
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-20T14:59:26.630991+00:00
-- url     : https://prove2.me/theorems/8d2326d4-a899-4640-9acc-1c35f1bbad4a
-- title:
--   Theorem 1 (production stage): the UB policy is optimal for any $J$ with the Lemma 3(a) properties
-- statement:
--   This is the production-stage content of Theorem 1, stated for an abstract single-period production objective.
--
--   Let $J:\mathbb R_+^2\to\mathbb R$ be convex, continuous, and supermodular on $\mathbb R_+^2$, and coercive along each coordinate: for every $v\ge0$,
--   $$
--   \lim_{s\to\infty}J(s,v)=\lim_{s\to\infty}J(v,s)=+\infty .
--   $$
--   These are exactly the properties of $J_t$ given by Lemma 3(a). Let $0<a^1<a^2$. Then there exist non-increasing switching curves $\gamma^1,\gamma^2:\mathbb R_+\to\mathbb R_+$, balancing curves $\alpha,\beta:\mathbb R_+\to\mathbb R_+^2$, and a common point $\bar w\in\mathbb R_+^2$ with the following properties.
--
--   1. **Meeting and minimization (eqs. (11)–(14)).** $\gamma^1(\bar w^2)=\bar w^1$, $\gamma^2(\bar w^1)=\bar w^2$, $\alpha(a^1\bar w^1+a^2\bar w^2)=\beta(\bar w^1+\bar w^2)=\bar w$. The point $\bar w$ minimizes $J$ on $\mathbb R_+^2$. Each $\gamma^j(s)$ minimizes $J$ over its coordinate with the other coordinate fixed at $s$. For every $x\ge0$, $\alpha(x)$ minimizes $J$ on $\{w\ge0: a^1w^1+a^2w^2=x\}$ and $\beta(x)$ minimizes $J$ on $\{w\ge0: w^1+w^2=x\}$.
--   2. **Regions.** For every demand $D\ge0$ and capacity $R\ge0$, the regions $\mathcal R_0,\dots,\mathcal R_5$ of Definition 1 cover $\mathbb R_+^2$. They are pairwise disjoint when $a^1R<D$.
--   3. **Optimality.** For every inventory $y\in\mathbb R_+^2$, the UB decision $w^*(y,D,R)$ of Definition 1 is feasible and optimal:
--   $$
--   w^*(y,D,R)\in\operatorname*{arg\,min}_{w\in E_2(y,D,R)}J(w).
--   $$
--
--   Theorem 1 follows by applying this result to $J=J_t$. Lemma 3(a) and the backward induction for $H_t$ show that $J_t$ has the required properties. In the paper this step is Section 4.3: Propositions 1–2 and the remark after Proposition 2, which reduces each balancing region to a one-variable convex problem.
--
--   **Formalization Note** The objective is abstracted by `IsJClass`, the predicate used in the milestones `proposition_1` and `proposition_2`. The curves, regions, and UB rule are those of `Def_RawBlending_UB_Policy`. Where the low-demand regions overlap, the rule takes the first matching region in printed order, as in `theorem_1`.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), pp. 15–16 (PDF 15–16), Theorem 1 (production part), proved in §4 via Propositions 1–2 (pp. 20–22) using only the Lemma 3(a) properties of J_t; cf. accepted version (MSOM 2022, doi:10.1287/msom.2021.1059), §4.3, remark after Proposition 2

import Mathlib
import Definitions.Def_RawBlending_UB_Policy

namespace RawBlending.UB

theorem theorem_1_production (Jobj : Vec → ℝ) (hJ : IsJClass Jobj)
    (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : a1 < a2) :
    ∃ C : Curves, IsUBCurves Jobj a1 a2 C ∧
      ∀ D R : ℝ, 0 ≤ D → 0 ≤ R →
        RegionsCover C a1 a2 D R ∧
        (a1 * R < D → RegionsDisjoint C a1 a2 D R) ∧
        ∀ y : Vec, y ∈ orthant →
          Minimizes Jobj (E2 a1 a2 y D R) (ubAction C a1 a2 D R y) := by sorry

end RawBlending.UB
