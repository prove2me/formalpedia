-- Prove2me | Theorems.Thm_ProEtale_isAdicComplete_iff_isHausdorff_and_isDerivedComplete
-- name    : ProEtale.isAdicComplete_iff_isHausdorff_and_isDerivedComplete
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-26T12:32:14.462772+00:00
-- url     : https://prove2.me/theorems/72022e81-8429-4d1c-b08b-115695bc54b4
-- title:
--   Proposition 3.4.2 (topos of sets) — classically complete means separated and derived complete
-- statement:
--   Let $R$ be a commutative ring, $I \subseteq R$ a finitely generated ideal and $M$ an $R$-module. Recall that $M$ is **classically $I$-complete** if the natural map $M \to \varprojlim_n M/I^nM$ is an isomorphism, **$I$-adically separated** if $\bigcap_n I^nM = 0$, and **derived $I$-complete** if for every $x \in I$ the endomorphism $(m_n)_n \mapsto (m_n - x\,m_{n+1})_n$ of $M^{\mathbb N}$ is bijective, i.e. the derived limit of the tower $\cdots \xrightarrow{x} M \xrightarrow{x} M$ vanishes.
--
--   Then
--
--   $$
--   M \text{ is classically } I\text{-complete} \iff M \text{ is } I\text{-adically separated and derived } I\text{-complete}.
--   $$
--
--   The proposition is what allows one to pass between the two notions of completeness; the paper notes that the two conditions on the right are not redundant.
--
--   **Formalization Note** The paper states the result for a module over a sheaf of rings $R$ with a locally finitely generated ideal $I$ in an arbitrary replete topos. The Lean statement is the case of the topos of sets, where this means an ordinary ring with a finitely generated ideal. Classical completeness is Mathlib's `IsAdicComplete I M` and separatedness is `IsHausdorff I M`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Proposition 3.4.2 with Definition 3.4.1 (p. 21 of the arXiv v2 PDF), in the case X = Set. Related formal material, for a principal ideal and in a different framework: leanprover-community/riemann-hypothesis, branch main (Apache-2.0, Lean v4.37.0-rc1; readable edition of the Alpöge–Claude formalization), file src/Lib/PadicComparison/Completion.lean.

import Mathlib
import Definitions.Def_ProEtale_DerivedComplete

universe u v

theorem ProEtale.isAdicComplete_iff_isHausdorff_and_isDerivedComplete {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I M ↔ IsHausdorff I M ∧ ProEtale.IsDerivedComplete I M := by sorry
