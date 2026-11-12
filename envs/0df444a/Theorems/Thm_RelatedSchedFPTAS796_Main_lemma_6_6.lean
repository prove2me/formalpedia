-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_6_6
-- name    : RelatedSchedFPTAS796.Main.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:30.33495+00:00
-- url     : https://prove2.me/theorems/3da3ab18-636e-4523-b6e1-7728d7f86473
-- title:
--   Lemma 6.6 ([AK08]) — every finite $A\subseteq\mathbb R^d$ of full rank has a barycentric spanner
-- statement:
--   For every finite set $A\subseteq\mathbb R^d$ containing $d$ linearly independent vectors, there is a subset $B=\{b_1,\dots,b_d\}\subseteq A$ that is a barycentric spanner of $A$: the $b_i$ are linearly independent and
--   $$A\subseteq\Big\{\sum_{i=1}^d x_ib_i:\ |x_i|\le1\Big\}.$$
--
--   The spanner supplies the modulus lattice $\Lambda=\mathrm{span}_{\mathbb Z}\{b_1,\dots,b_d\}$ in the proof of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: a subset $B\subseteq A$ of $d$ linearly independent vectors → a linearly independent family $b:\{1..d\}\to A$; reason: a linearly independent family is injective, so it is the same as a $d$-element subset
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.19, Lemma 6.6 ([AK08], Awerbuch–Kleinberg) and Definition 6.5

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Lattice

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 6.6 ([AK08])**, p.19. Every finite set `A ⊆ ℝ^d` containing `d` linearly independent
vectors has a subset `{b_1, …, b_d} ⊆ A` that is a barycentric spanner of `A` (Definition 6.5). -/
theorem lemma_6_6 {d : ℕ} (A : Set (Fin d → ℝ)) (hA : A.Finite)
    (hli : ∃ v : Fin d → Fin d → ℝ, LinearIndependent ℝ v ∧ ∀ i, v i ∈ A) :
    ∃ b : Fin d → Fin d → ℝ, IsBarycentricSpanner A b := by sorry

end RelatedSchedFPTAS796.Main
