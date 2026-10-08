-- Prove2me | Theorems.Thm_TreewidthApprox_TreeMeasure_case_one
-- name    : TreewidthApprox.TreeMeasure.case_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:49.901708+00:00
-- url     : https://prove2.me/theorems/643685b3-9a35-4629-8d44-ede204be6344
-- title:
--   Proof of Lemma 4.3, p. 350 — case p = 1: one child gives the bound at v
-- statement:
--   Let $T$ be a finite rooted tree with root $r$, let $\mu : V(T) \to \mathbb R$ and $0 < C < 1$ satisfy the hypotheses (i)–(iii) of Lemma 4.3, and write $K = 1 + \frac{1}{1-C}$. Let $v$ be a vertex with exactly one child $v_1$, and suppose that $|V(T_{v_1})| \le K\mu(v_1) - 1$. Then
--   $$
--   |V(T_v)| \;\le\; \Bigl(1 + \frac{1}{1-C}\Bigr)\mu(v) - 1 .
--   $$
--
--   This is the second of the two cases of the induction step in the proof of Lemma 4.3; it uses hypothesis (iii) on the edge from $v$ to $v_1$ and hypothesis (i) at $v$.
--
--   **Formalization Note** $|V(T_v)|$ is the subtree size $\mathrm{size}_T(v)$ of the referenced rooted-tree definition. The paper states the step at the root of the whole tree; here it is stated at an arbitrary vertex $v$. The induction hypothesis is stated for every child of $v$, of which there is exactly one.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 350, proof of Lemma 4.3, case p = 1 (third display)

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_TreewidthApprox_TreeMeasure_Setting

namespace TreewidthApprox.TreeMeasure

open HarelTarjan.Compressed

theorem case_one {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V) (hp : (children T v).card = 1)
    (hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1) :
    (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by sorry

end TreewidthApprox.TreeMeasure
