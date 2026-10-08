-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_larger_uncertainty
-- name    : RobustMNL.Dynamic.larger_uncertainty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:15.336538+00:00
-- url     : https://prove2.me/theorems/0baafc7c-ad06-4726-a429-cb5fea9e55fe
-- title:
--   Corollary 3.5 (restated) — larger uncertainty implies a larger robust assortment: Z*(V′) ≤ Z*(V), S*(V) ⊆ S*(V′)
-- statement:
--   Let $\mathcal V \subseteq \mathcal V' \subseteq \mathbb R^{n+1}_{++}$ be compact, with $\mathcal V$ nonempty, and let $r$ be arbitrary real revenues. Then
--   $$Z^*(\mathcal V') \le Z^*(\mathcal V) \qquad\text{and}\qquad S^*(\mathcal V) \subseteq S^*(\mathcal V'),$$
--   the latter for every optimal assortment of smallest cardinality $S^*(\mathcal V)$ over $\mathcal V$ and every one $S^*(\mathcal V')$ over $\mathcal V'$.
--
--   In Section 4 the inclusion compares the robust assortments of periods $t$ and $t+1$ when $\mathcal V_t \subseteq \mathcal V_{t+1}$.
--
--   **Formalization Note** The paper writes "$V \subseteq V' \subseteq \mathbb R^n_{++}$"; it is read as subsets of $\mathbb R^{n+1}_{++}$, compact by the standing assumption of Sec. 3. The proof of Theorem 4.3 (p. 18) cites Theorem 3.6 for this inclusion; the inclusion it uses is exactly this corollary's. This restates `RobustMNL.Static.larger_uncertainty` of the companion mission verbatim up to namespace.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Corollary 3.5, p. 9

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_StaticModel

namespace RobustMNL.Dynamic

theorem larger_uncertainty {n : ℕ} (r : Fin n → ℝ) (V V' : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, RobustMNL.Static.IsPos p)
    (hV' : IsCompact V') (hpos' : ∀ p ∈ V', RobustMNL.Static.IsPos p) (hsub : V ⊆ V') :
    RobustMNL.Static.Zstar V' r ≤ RobustMNL.Static.Zstar V r ∧
      ∀ S S' : Finset (Fin n), RobustMNL.Static.IsSmallestOptimal V r S → RobustMNL.Static.IsSmallestOptimal V' r S' → S ⊆ S' := by sorry

end RobustMNL.Dynamic
