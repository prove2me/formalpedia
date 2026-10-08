-- Prove2me | Theorems.Thm_TreewidthApprox_TreeMeasure_case_two_or_more
-- name    : TreewidthApprox.TreeMeasure.case_two_or_more
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:52.638993+00:00
-- url     : https://prove2.me/theorems/a741613c-4320-43d1-8d59-26d3b9900ed6
-- title:
--   Proof of Lemma 4.3, p. 350 — case p ≥ 2: at least two children give the bound at v
-- statement:
--   Let $T$ be a finite rooted tree with root $r$, let $\mu : V(T) \to \mathbb R$ and $0 < C < 1$ satisfy the hypotheses (i)–(iii) of Lemma 4.3, and write $K = 1 + \frac{1}{1-C}$. Let $v$ be a vertex with $p \ge 2$ children $v_1,\dots,v_p$, and suppose that every subtree rooted at a child satisfies $|V(T_{v_i})| \le K\mu(v_i) - 1$. Then the subtree rooted at $v$ satisfies
--   $$
--   |V(T_v)| \;\le\; \Bigl(1 + \frac{1}{1-C}\Bigr)\mu(v) - 1 .
--   $$
--
--   This is the first of the two cases of the induction step in the proof of Lemma 4.3; it uses hypothesis (ii) at $v$.
--
--   **Formalization Note** $|V(T_v)|$ is the subtree size $\mathrm{size}_T(v)$ of the referenced rooted-tree definition and $p$ is the number of children of $v$. The paper states the step at the root of the whole tree; here it is stated at an arbitrary vertex $v$.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 350, proof of Lemma 4.3, case p ≥ 2 (second display)

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_TreewidthApprox_TreeMeasure_Setting

namespace TreewidthApprox.TreeMeasure

open HarelTarjan.Compressed

theorem case_two_or_more {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V) (hp : 2 ≤ (children T v).card)
    (hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1) :
    (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by sorry

end TreewidthApprox.TreeMeasure
