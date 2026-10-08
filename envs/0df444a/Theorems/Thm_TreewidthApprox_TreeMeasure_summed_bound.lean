-- Prove2me | Theorems.Thm_TreewidthApprox_TreeMeasure_summed_bound
-- name    : TreewidthApprox.TreeMeasure.summed_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:47.929869+00:00
-- url     : https://prove2.me/theorems/462bf229-54cc-478f-b1ce-d19cc185dde3
-- title:
--   Proof of Lemma 4.3, p. 350 — summing the bounds for the children's subtrees: |V(T)| ≤ 1 − p + (1 + 1/(1−C)) Σ μ(vᵢ)
-- statement:
--   Let $T$ be a finite rooted tree with root $r$, let $\mu : V(T) \to \mathbb R$ and $0 < C < 1$ satisfy the hypotheses (i)–(iii) of Lemma 4.3, and write
--   $$
--   K = 1 + \frac{1}{1-C}.
--   $$
--   Let $v$ be a vertex with children $v_1,\dots,v_p$ ($p \ge 0$), and let $T_v$ and $T_{v_1},\dots,T_{v_p}$ be the subtrees rooted at $v$ and at its children. If every child satisfies $|V(T_{v_i})| \le K\mu(v_i) - 1$, then
--   $$
--   |V(T_v)| \;\le\; 1 - p + K \sum_{i=1}^{p} \mu(v_i) .
--   $$
--
--   This is the inequality obtained in the induction step of the proof of Lemma 4.3 by summing the induction hypotheses for the subtrees rooted at the children; its content is that $V(T_v)$ is $\{v\}$ together with the disjoint union of the $V(T_{v_i})$.
--
--   **Formalization Note** $|V(T_v)|$ is the subtree size $\mathrm{size}_T(v)$ of the referenced rooted-tree definition; $p$ is the number of children of $v$. The paper states the step at the root of the whole tree; stating it at an arbitrary vertex $v$ of a fixed tree is the same statement for the subtree $T_v$. Hypotheses (i)–(iii) are carried for uniformity although this step does not use them.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 350, proof of Lemma 4.3, first paragraph and first display

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_TreewidthApprox_TreeMeasure_Setting

namespace TreewidthApprox.TreeMeasure

open HarelTarjan.Compressed

theorem summed_bound {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V)
    (hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1) :
    (size T v : ℝ) ≤
      1 - ((children T v).card : ℝ) + (1 + 1 / (1 - C)) * ∑ c ∈ children T v, μ c := by sorry

end TreewidthApprox.TreeMeasure
