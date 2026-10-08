-- Prove2me | Theorems.Thm_QLLL_lll_iInf
-- name    : QLLL.lll_iInf
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:47:25.765156+00:00
-- url     : https://prove2.me/theorems/b1d244de-487f-4186-a787-b03af556fffd
-- title:
--   Local lemma for an infinite index set, under continuity from above
-- statement:
--   Let $L$ be a complete lattice and $R : L \to \mathbb{R}$ a valuation (nonnegative, monotone, modular, $R(\top) = 1$, $R(\bot) = 0$). Let $(X_i)_{i \in I}$ be a family in $L$ indexed by an arbitrary set $I$, and let $\Gamma(i) \subseteq I$ be finite sets forming a dependency graph: for every $i$ and every finite $S \subseteq I$ with $i \notin S$ and $S \cap \Gamma(i) = \emptyset$, $R\big(X_i \wedge \bigwedge_{j \in S} X_j\big) = R(X_i)\,R\big(\bigwedge_{j \in S} X_j\big)$. Let $0 \le y_i < 1$ with $R(X_i) \ge 1 - y_i \prod_{j \in \Gamma(i)} (1 - y_j)$ for every $i$, and let $c$ be a real number with $c \le \prod_{j \in S}(1 - y_j)$ for every finite $S \subseteq I$. Assume $R$ is continuous from above in the following sense: whenever $b \le R\big(\bigwedge_{j \in S} X_j\big)$ for every finite $S \subseteq I$, also $b \le R\big(\bigwedge_{i \in I} X_i\big)$.
--
--   Then
--   $$c \ \le\ R\Big(\bigwedge_{i \in I} X_i\Big).$$
--
--   This extends Theorem 14 of Ambainis, Kempe and Sattath to infinite families. The continuity hypothesis is exactly what is needed: it holds for a normal trace, but fails for relative dimension in infinite dimension, where nonzero subspaces can have all finite intersections nonzero and zero total intersection.
-- source:
--   Not in the paper; an extension of Theorem 14 to infinite index sets. Formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_LocalLemma_Infinite
import Mathlib

open QLLL
open Finset
variable {α : Type*} [CompleteLattice α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

theorem QLLL.lll_iInf (hΓ : IsDependencyGraphOn R X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ R (X i))
    (c : ℝ) (hc : ∀ S : Finset ι, c ≤ ∏ j ∈ S, (1 - y j))
    (hcont : ∀ b : ℝ, (∀ S : Finset ι, b ≤ R (S.inf X)) → b ≤ R (⨅ i, X i)) :
    c ≤ R (⨅ i, X i) := by sorry
