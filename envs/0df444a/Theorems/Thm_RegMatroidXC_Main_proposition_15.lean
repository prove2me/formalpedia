-- Prove2me | Theorems.Thm_RegMatroidXC_Main_proposition_15
-- name    : RegMatroidXC.Main.proposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:49.961513+00:00
-- url     : https://prove2.me/theorems/ee765273-51c7-4126-93d0-be4d02432615
-- title:
--   Proposition 15 (the "in particular" bound) — xc(P(M)) ≤ xc(P_{T}(M₀), Q_{T}(M₀)) + 16 Σᵢ xc(P(Mᵢ))
-- statement:
--   Let $M \overset{\star}{=} M_0 \oplus_3 M_1 \oplus_3 \cdots \oplus_3 M_k$ be a loopless matroid obtained from binary matroids $M_0, M_1, \dots, M_k$, with $M_1, \dots, M_k$ mutually disjoint, by simultaneously performing a 3-sum of $M_0$ with each $M_i$ along the triangle $T_i = E(M_0) \cap E(M_i) = \{\alpha_i, \beta_i, \gamma_i\}$. Let $R$ be any polytope with
--   $$P_{T_1,\dots,T_k}(M_0) \subseteq R \subseteq Q_{T_1,\dots,T_k}(M_0).$$
--   Then
--   $$\mathrm{xc}(P(M)) \le \mathrm{xc}(R) + 16 \sum_{i=1}^k \mathrm{xc}(P(M_i)),$$
--   and hence $\mathrm{xc}(P(M)) \le \mathrm{xc}(P_{T_1,\dots,T_k}(M_0), Q_{T_1,\dots,T_k}(M_0)) + 16 \sum_{i=1}^k \mathrm{xc}(P(M_i))$. Precisely: if $R$ has an extended formulation with $r_0$ inequalities and each $P(M_i)$ has one with $r_i$ inequalities, then $P(M)$ has one with at most $r_0 + 16 \sum_i r_i$ inequalities.
--
--   This reduces a formulation for the whole star decomposition to a formulation for the pair of polytopes attached to the centre $M_0$; Propositions 16 and 18 supply that formulation when $M_0$ is graphic or cographic.
--
--   **Formalization Note** Only the "In particular" bound of Proposition 15 is stated; the description (3) of $P(M)$ through the polytopes $P'(M_i), P''(M_i)$ of Proposition 13 is not. The bound holds for every naming of the triangle elements (on which $P_{T_1,\dots,T_k}(M_0)$ depends). $R$ ranges over all sets with an extended formulation between the two polytopes; such a set is automatically a polytope. Looplessness is the paper's standing assumption (end of §4.1, p. 5).
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 8, Proposition 15 (the "In particular" bound)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums
import Definitions.Def_RegMatroidXC_Main_Pairs
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem proposition_15 (α : Type) (M M₀ : Matroid α) (k : ℕ) (Ms : Fin k → Matroid α)
    [Fintype M.E] [Fintype M₀.E] [∀ i, Fintype (Ms i).E]
    (hloop : M.Loopless) (hdec : IsStarDecomposition M M₀ Ms)
    (tri : Fin k → Fin 3 → α)
    (htri : ∀ i, Function.Injective (tri i) ∧ triSet tri i = M₀.E ∩ (Ms i).E)
    (R : Set (PairIdx M₀ tri → ℝ)) (hPR : PolyP M₀ tri ⊆ R) (hRQ : R ⊆ PolyQ M₀ tri)
    (r₀ : ℕ) (hR : IsEFOfSize R r₀)
    (r : Fin k → ℕ) (hr : ∀ i, IsEFOfSize (indepPolytope (Ms i)) (r i)) :
    ∃ s : ℕ, IsEFOfSize (indepPolytope M) s ∧ s ≤ r₀ + 16 * ∑ i, r i := by sorry

end RegMatroidXC.Main
