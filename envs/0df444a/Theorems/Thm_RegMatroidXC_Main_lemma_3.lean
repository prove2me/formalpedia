-- Prove2me | Theorems.Thm_RegMatroidXC_Main_lemma_3
-- name    : RegMatroidXC.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:28.831882+00:00
-- url     : https://prove2.me/theorems/eea07a38-c64c-4427-afd7-84d40fb64b69
-- title:
--   Lemma 3 — for t ∈ {1, 2}, xc(P(M₁ ⊕ₜ M₂)) ≤ xc(P(M₁)) + xc(P(M₂))
-- statement:
--   Let $M_1, M_2$ be binary matroids and let $M = M_1 \oplus_t M_2$ be their 1-sum or 2-sum ($t \in \{1, 2\}$), with all the side conditions of the definition. Then
--   $$\mathrm{xc}(P(M_1 \oplus_t M_2)) \le \mathrm{xc}(P(M_1)) + \mathrm{xc}(P(M_2)).$$
--   Precisely: if $P(M_1)$ and $P(M_2)$ have extended formulations with $r_1$ and $r_2$ inequalities, then $P(M)$ has one with at most $r_1 + r_2$ inequalities.
--
--   This handles the 1- and 2-sum cases of the induction in the main theorem.
--
--   **Formalization Note** The bound is quantified over extended formulations of the parts, so it never mentions the value of $\mathrm{xc}$ on a set without an extended formulation.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 2, Lemma 3

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem lemma_3 (α : Type) (M M₁ M₂ : Matroid α) [Fintype M.E] [Fintype M₁.E] [Fintype M₂.E]
    (hsum : IsOneSum M M₁ M₂ ∨ IsTwoSum M M₁ M₂) (r₁ r₂ : ℕ)
    (h₁ : IsEFOfSize (indepPolytope M₁) r₁) (h₂ : IsEFOfSize (indepPolytope M₂) r₂) :
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ r ≤ r₁ + r₂ := by sorry

end RegMatroidXC.Main
