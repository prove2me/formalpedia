-- Prove2me | Theorems.Thm_WeightedEdgeColor_Supplement_theorem_1_1_optimality
-- name    : WeightedEdgeColor.Supplement.theorem_1_1_optimality
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:38:15.714967+00:00
-- url     : https://prove2.me/theorems/6da149d5-8251-432a-974a-9fb88a4c1cec
-- title:
--   Theorem 1.1 (closing sentence) — the coefficients $1$ ($\mathrm{bp}$, simple), $2$ ($\Delta_w$, bipartite), $3$ ($\lceil\Delta_w\rceil$, loopless) are optimal
-- statement:
--   The leading coefficients of three bounds in Theorem 1.1 cannot be lowered, for any additive constant:
--
--   1. **(coefficient one, simple graphs)** for every $c<1$ and every real $C$ there is a finite simple weighted graph $G$ with $\chi'_w(G)>c\,\mathrm{bp}(G)+C$;
--   2. **(coefficient two, bipartite multigraphs)** for every $c<2$ and every real $C$ there is a finite bipartite weighted multigraph $G$ with $\chi'_w(G)>c\,\Delta_w(G)+C$;
--   3. **(coefficient three, loopless multigraphs)** for every $c<3$ and every real $C$ there is a finite loopless weighted multigraph $G$ with
--   $$
--   \chi'_w(G)>c\,\lceil\Delta_w(G)\rceil+C .
--   $$
--
--   Here $\chi'_w(G)$ is the least number of colors in a proper weighted coloring (every color class has incident weight at most one at every vertex), $\mathrm{bp}(G)$ is the local bin-packing number and $\Delta_w(G)$ the maximum weighted degree; all weights lie in $(0,1]$.
--
--   Together with the upper bounds $(1+o(1))\mathrm{bp}(G)$ for simple graphs, $(2+o(1))\Delta_w(G)$ for bipartite multigraphs and $3\lceil\Delta_w(G)\rceil$ for loopless multigraphs, this says those three bounds are tight in their leading coefficient.
--
--   **Formalization Note** "$\chi'_w(G)>Y$" is stated as "every proper weighted coloring with $k$ colors has $Y<k$".
--
--   Differences from the source:
--   - reading: the coefficient one for simple graphs and the total-weight coefficients two and three are optimal → three lower-bound families: for every $c$ below the coefficient and every real $C$ a graph of the class with $\chi'_w(G)>c\,X(G)+C$, with $X=\mathrm{bp}$, $\Delta_w$, $\lceil\Delta_w\rceil$ for simple graphs, bipartite multigraphs, loopless multigraphs respectively; reason: the sentence refers to the asymptotic bounds of the table (footnote 2); a coefficient is optimal when no bound with a smaller coefficient holds for any additive constant; this is the stronger reading (not only $C=0$)
--   - encoding: $\chi'_w(G)>Y$ → every proper weighted coloring $E\to\{0,\dots,k-1\}$ has $Y<k$; reason: $\chi'_w(G)$ is the least such $k$
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem 1.1 (closing sentence) with footnote 2, p.2; sharpness examples: the star of §1 p.1 and §5 p.13, the triangle of §B.4 p.32

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_WeightedEdgeColor_WGraph_bp
import Definitions.Def_WeightedEdgeColor_Supplement_maxWDeg
import Definitions.Def_WeightedEdgeColor_Supplement_IsBipartite

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- Theorem 1.1, closing sentence: "The coefficient one for simple graphs and the total-weight
coefficients two and three are optimal." For every `c` below the coefficient and every additive
constant `C` there is a graph of the class with `χ′_w(G) > c·X(G) + C`:
1. coefficient one, simple graphs, `X = bp(G)`;
2. coefficient two, bipartite multigraphs, `X = ∆_w(G)`;
3. coefficient three, loopless multigraphs, `X = ⌈∆_w(G)⌉`.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem 1.1 (closing sentence) with footnote 2, p.2; sharpness examples §5 p.13 and §B.4 p.32.

**Formalization Note.** `χ′_w(G) > Y` is "every proper weighted coloring `E → Fin k` has
`Y < k`". Optimality of a coefficient in an asymptotic bound `(c₀ + o(1))X` (footnote 2) is
read as: for every `c < c₀` and every `C`, the bound `c·X + C` fails on some graph of the
class. -/
theorem theorem_1_1_optimality :
    (∀ c : ℝ, c < 1 → ∀ C : ℝ, ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V)
      (_ : Fintype E) (_ : DecidableEq E) (G : WGraph V E), G.IsSimple ∧
      ∀ (k : ℕ) (φ : E → Fin k), G.IsProperColoring φ → c * (G.bp : ℝ) + C < k) ∧
    (∀ c : ℝ, c < 2 → ∀ C : ℝ, ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V)
      (_ : Fintype E) (_ : DecidableEq E) (G : WGraph V E), IsBipartite G ∧
      ∀ (k : ℕ) (φ : E → Fin k), G.IsProperColoring φ → c * maxWDeg G + C < k) ∧
    (∀ c : ℝ, c < 3 → ∀ C : ℝ, ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V)
      (_ : Fintype E) (_ : DecidableEq E) (G : WGraph V E),
      ∀ (k : ℕ) (φ : E → Fin k), G.IsProperColoring φ →
        c * ((⌈maxWDeg G⌉ : ℤ) : ℝ) + C < k) := by sorry

end Supplement

end WeightedEdgeColor
