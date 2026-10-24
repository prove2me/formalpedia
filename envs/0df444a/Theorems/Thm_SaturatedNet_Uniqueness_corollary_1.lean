-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_corollary_1
-- name    : SaturatedNet.Uniqueness.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:33.217738+00:00
-- url     : https://prove2.me/theorems/044f6f31-8536-43a9-b006-65cf48be45cc
-- title:
--   Corollary 1, pp. 12–13 — one node partition on which every equilibrium of a non-expansive network solves the linear system (27)
-- statement:
--   Let $(P, w)$ be a non-expansive network and $c \in \mathbb R^n$ any exogenous flow. Then there is a
--   partition $\mathcal V = \mathcal V_+ \cup \mathcal V_0 \cup \mathcal V_-$ of the nodes into three
--   pairwise disjoint sets such that, writing $z = (z^{(+)}, z^{(0)}, z^{(-)})$ for the corresponding
--   split of a vector and $P^{(\alpha\beta)}$ for the block of $P$ with rows in $\mathcal V_\alpha$ and
--   columns in $\mathcal V_\beta$:
--
--   1. every network equilibrium $x$ satisfies
--      $$x^{(-)} = 0,\qquad x^{(0)} = P^{(00)\top}x^{(0)} + P^{(+0)\top}x^{(+)} + c^{(0)},\qquad x^{(+)} = w^{(+)};$$
--   2. any two network equilibria $x, y$ satisfy $x^{(-)} = y^{(-)}$ and $x^{(+)} = y^{(+)}$.
--
--   The partition is the same for all equilibria; uniqueness can therefore be decided on the exposed
--   block, where equilibria solve a linear system. It is the reduction used in Propositions 4 and 5.
--
--   **Formalization Note.** The middle equation is written coordinatewise: for $i \in \mathcal V_0$,
--   $x_i = \sum_{k \in \mathcal V_0} P_{ki}x_k + \sum_{k \in \mathcal V_+} P_{ki}x_k + c_i$. The partition
--   is a single triple of sets chosen before the equilibria, not a function of $x$.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, pp. 12–13, Corollary 1, (26)–(28)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem corollary_1 {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hne : IsNonExpansive P) :
    ∃ Vp V0 Vm : Finset n,
      Disjoint Vp V0 ∧ Disjoint Vp Vm ∧ Disjoint V0 Vm ∧ Vp ∪ V0 ∪ Vm = Finset.univ ∧
      (∀ x ∈ equilibria P w c,
        (∀ i ∈ Vm, x i = 0) ∧
        (∀ i ∈ V0, x i = ∑ k ∈ V0, P k i * x k + ∑ k ∈ Vp, P k i * x k + c i) ∧
        (∀ i ∈ Vp, x i = w i)) ∧
      (∀ x ∈ equilibria P w c, ∀ y ∈ equilibria P w c,
        (∀ i ∈ Vm, x i = y i) ∧ (∀ i ∈ Vp, x i = y i)) := by sorry

end SaturatedNet.Uniqueness
