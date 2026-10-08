-- Prove2me | Theorems.Thm_TreewidthApprox_TreeMeasure_base_case
-- name    : TreewidthApprox.TreeMeasure.base_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:39.445951+00:00
-- url     : https://prove2.me/theorems/757dc863-d84c-42cc-a80a-2167f5f743f9
-- title:
--   Proof of Lemma 4.3, p. 349 — base case: a single-vertex (sub)tree satisfies the bound by (i)
-- statement:
--   Let $T$ be a finite rooted tree with root $r$, and let $\mu : V(T) \to \mathbb R$ and $0 < C < 1$ satisfy the hypotheses of Lemma 4.3:
--
--   1. $\mu(v) \ge 1$ for every vertex $v$;
--   2. $\sum_{c \in \mathrm{ch}(v)} \mu(c) \le \mu(v)$ for every vertex $v$, where $\mathrm{ch}(v)$ is the set of children of $v$;
--   3. $\mu(c) \le C\,\mu(v)$ whenever $v$ is the parent of $c$.
--
--   If a vertex $v$ has no children, then the subtree $T_v$ rooted at $v$ consists of $v$ alone and satisfies the bound of Lemma 4.3:
--   $$
--   |V(T_v)| \;\le\; \Bigl(1 + \frac{1}{1-C}\Bigr)\mu(v) - 1 .
--   $$
--
--   This is the base case of the induction on the size of the tree in the proof of Lemma 4.3.
--
--   **Formalization Note** $|V(T_v)|$ is the subtree size $\mathrm{size}_T(v)$ of the referenced rooted-tree definition (the number of descendants of $v$, including $v$). The paper's base case is a tree with one vertex; here it is a leaf $v$ of a fixed tree $T$, whose subtree is that one-vertex tree. Hypotheses (ii) and (iii) are carried for uniformity with the other steps of the proof.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 349, proof of Lemma 4.3, first paragraph (base case |V(T)| = 1)

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_TreewidthApprox_TreeMeasure_Setting

namespace TreewidthApprox.TreeMeasure

open HarelTarjan.Compressed

theorem base_case {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V) (hleaf : children T v = ∅) :
    (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by sorry

end TreewidthApprox.TreeMeasure
