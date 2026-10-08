-- Prove2me | Theorems.Thm_QLLL_iInf_ne_bot
-- name    : QLLL.iInf_ne_bot
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:29.805976+00:00
-- url     : https://prove2.me/theorems/04688c0e-8a2b-43f2-9adf-f9d3e17fa4a2
-- title:
--   Local lemma for an infinite index set: the whole family has a nonzero meet
-- statement:
--   Let $L$ be a complete lattice and $R : L \to \mathbb{R}$ a valuation (nonnegative, monotone, modular, $R(\top) = 1$, $R(\bot) = 0$). Let $(X_i)_{i \in I}$ be a family in $L$ indexed by an arbitrary set $I$, and let $\Gamma(i) \subseteq I$ be finite sets forming a dependency graph: for every $i$ and every finite $S \subseteq I$ with $i \notin S$ and $S \cap \Gamma(i) = \emptyset$, $R\big(X_i \wedge \bigwedge_{j \in S} X_j\big) = R(X_i)\,R\big(\bigwedge_{j \in S} X_j\big)$. Let $0 \le y_i < 1$ with $R(X_i) \ge 1 - y_i \prod_{j \in \Gamma(i)} (1 - y_j)$ for every $i$, and let $c$ be a real number with $c \le \prod_{j \in S}(1 - y_j)$ for every finite $S \subseteq I$. Assume $R$ is continuous from above in the following sense: whenever $b \le R\big(\bigwedge_{j \in S} X_j\big)$ for every finite $S \subseteq I$, also $b \le R\big(\bigwedge_{i \in I} X_i\big)$. Suppose moreover that $c > 0$.
--
--   Then
--   $$\bigwedge_{i \in I} X_i \ \neq\ \bot.$$
--
--   This is the qualitative conclusion of `QLLL.lll_iInf`: under the same hypotheses and a positive lower bound $c$ on the finite products, the meet of the whole family is not the bottom element.
-- source:
--   Not in the paper; an extension of Theorem 14 to infinite index sets. Formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_LocalLemma_Infinite
import Mathlib

open QLLL
open Finset
variable {α : Type*} [CompleteLattice α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

theorem QLLL.iInf_ne_bot (hΓ : IsDependencyGraphOn R X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ R (X i))
    (c : ℝ) (hc : ∀ S : Finset ι, c ≤ ∏ j ∈ S, (1 - y j)) (hcpos : 0 < c)
    (hcont : ∀ b : ℝ, (∀ S : Finset ι, b ≤ R (S.inf X)) → b ≤ R (⨅ i, X i)) :
    (⨅ i, X i) ≠ ⊥ := by sorry
