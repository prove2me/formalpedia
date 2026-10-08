-- Prove2me | Theorems.Thm_TreewidthApprox_TreeMeasure_lemma_4_3
-- name    : TreewidthApprox.TreeMeasure.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:57.141988+00:00
-- url     : https://prove2.me/theorems/29b9211f-5b1d-4584-8e19-ff758326eb98
-- title:
--   Lemma 4.3 — a rooted tree with a measure μ ≥ 1, superadditive over children and shrinking by C < 1 to each child, has at most (1 + 1/(1−C))μ(r) − 1 vertices
-- statement:
--   Let $T$ be a finite rooted tree with root $r$. Suppose $\mu : V(T) \to \mathbb R$ is a measure on its vertices and $C$ is a real constant with $0 < C < 1$ such that:
--
--   1. $\mu(v) \ge 1$ for every $v \in V(T)$;
--   2. for every vertex $v$ with children $v_1, v_2, \dots, v_p$ (possibly $p = 0$), $\sum_{i=1}^{p} \mu(v_i) \le \mu(v)$;
--   3. for every two vertices $v, v'$ such that $v$ is the parent of $v'$, $\mu(v') \le C \cdot \mu(v)$.
--
--   Then
--   $$
--   |V(T)| \;\le\; \Bigl(1 + \frac{1}{1-C}\Bigr)\mu(r) - 1 .
--   $$
--
--   In the paper this bounds the number of nodes of the partial tree decomposition built by the algorithm `FindPartialTD`, applied with $\mu(i) = w_i / \log n$; it turns a measure that is superadditive over children and decays geometrically along every root-to-leaf path into a linear bound on the size of the tree.
--
--   **Formalization Note** The rooted tree is the referenced `HarelTarjan.Compressed.RootedTree`: a finite vertex type $V$ with a root and a parent map in which every vertex reaches the root, with the convention $p(r) = r$; $|V(T)|$ is the cardinality of $V$. "$c$ is a child of $v$" means $c \ne r$ and $p(c) = v$. The paper's "there exists a constant $0 < C < 1$" is a given constant $C$ with hypotheses $0 < C$ and $C < 1$, because the conclusion is stated with that $C$; the hypothesis $C < 1$ also keeps the real division $1/(1-C)$ from being the Lean default $1/0 = 0$.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 349, Lemma 4.3

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_TreewidthApprox_TreeMeasure_Setting

namespace TreewidthApprox.TreeMeasure

open HarelTarjan.Compressed

theorem lemma_4_3 {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) :
    (Fintype.card V : ℝ) ≤ (1 + 1 / (1 - C)) * μ T.root - 1 := by sorry

end TreewidthApprox.TreeMeasure
