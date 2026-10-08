-- Prove2me | Theorems.Thm_RobustMNL_Static_larger_uncertainty
-- name    : RobustMNL.Static.larger_uncertainty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:24.856354+00:00
-- url     : https://prove2.me/theorems/a0c9eaf6-e6d5-45cd-bcca-ba4d253c72a1
-- title:
--   Corollary 3.5 — larger uncertainty implies larger robust assortment: Z*(𝒱′) ≤ Z*(𝒱), S*(𝒱) ⊆ S*(𝒱′)
-- statement:
--   **Larger uncertainty implies a larger robust assortment.** Let $\mathcal V \subseteq \mathcal V' \subseteq \mathbb R^{n+1}_{++}$ be compact uncertainty sets, with $\mathcal V$ nonempty. Then
--   $$Z^*(\mathcal V') \le Z^*(\mathcal V) \qquad\text{and}\qquad S^*(\mathcal V) \subseteq S^*(\mathcal V'),$$
--   where $S^*(\cdot)$ denotes any optimal robust assortment of smallest cardinality.
--
--   More uncertainty lowers the optimal worst-case revenue and enlarges the robust assortment: product variety acts as a buffer against uncertainty in the choice parameters.
--
--   **Formalization Note** The inclusion is stated for every pair $S, S'$ of smallest-cardinality optimal assortments for $\mathcal V$ and $\mathcal V'$. The page writes "$\mathcal V \subseteq \mathcal V' \subseteq \mathbb R^n_{++}$"; it is read, as in Theorem 3.2, as compact sets in $\mathbb R^{n+1}_{++}$ (the standing assumption of Sec. 3). Nonemptiness of $\mathcal V'$ follows from that of $\mathcal V$. Revenues are arbitrary reals; products are `Fin n`.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Corollary 3.5, p. 9

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Static

theorem larger_uncertainty {n : ℕ} (r : Fin n → ℝ) (V V' : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p)
    (hV' : IsCompact V') (hpos' : ∀ p ∈ V', IsPos p) (hsub : V ⊆ V') :
    Zstar V' r ≤ Zstar V r ∧
      ∀ S S' : Finset (Fin n), IsSmallestOptimal V r S → IsSmallestOptimal V' r S' → S ⊆ S' := by sorry

end RobustMNL.Static
