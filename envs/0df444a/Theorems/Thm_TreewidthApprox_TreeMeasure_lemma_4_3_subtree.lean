-- Prove2me | Theorems.Thm_TreewidthApprox_TreeMeasure_lemma_4_3_subtree
-- name    : TreewidthApprox.TreeMeasure.lemma_4_3_subtree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:47.667898+00:00
-- url     : https://prove2.me/theorems/82cefdaf-5cf6-4cb0-b2cd-43ee737ab437
-- title:
--   Proof of Lemma 4.3, p. 350 — the bound holds for the subtree rooted at every vertex
-- statement:
--   Let $T$ be a finite rooted tree with root $r$, and let $\mu : V(T) \to \mathbb R$ and $0 < C < 1$ satisfy the hypotheses of Lemma 4.3:
--
--   1. $\mu(v) \ge 1$ for every vertex $v$;
--   2. $\sum_{c \in \mathrm{ch}(v)} \mu(c) \le \mu(v)$ for every vertex $v$;
--   3. $\mu(c) \le C\,\mu(v)$ whenever $v$ is the parent of $c$.
--
--   Then for every vertex $v$ the subtree $T_v$ rooted at $v$ satisfies
--   $$
--   |V(T_v)| \;\le\; \Bigl(1 + \frac{1}{1-C}\Bigr)\mu(v) - 1 .
--   $$
--
--   The proof of Lemma 4.3 applies the lemma to the subtrees rooted at the children of the root (the "induction hypothesis"); this is that statement for all subtrees at once. At $v = r$ it is Lemma 4.3 itself.
--
--   **Formalization Note** $|V(T_v)|$ is the subtree size $\mathrm{size}_T(v)$ of the referenced rooted-tree definition (the descendants of $v$, including $v$).
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 350, proof of Lemma 4.3 (induction hypothesis applied to T_1, …, T_p)

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_TreewidthApprox_TreeMeasure_Setting

namespace TreewidthApprox.TreeMeasure

open HarelTarjan.Compressed

theorem lemma_4_3_subtree {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) :
    ∀ v, (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by sorry

end TreewidthApprox.TreeMeasure
