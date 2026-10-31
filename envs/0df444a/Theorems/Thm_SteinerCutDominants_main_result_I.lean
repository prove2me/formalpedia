-- Prove2me | Theorems.Thm_SteinerCutDominants_main_result_I
-- name    : SteinerCutDominants.main_result_I
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:23.211524+00:00
-- url     : https://prove2.me/theorems/778b34d9-943a-48d6-b103-7433e1d8e440
-- title:
--   Main Result I: finite generation of the facets of Steiner cut dominants
-- statement:
--   For each integer $\tau$ there is a finite set $\mathcal F$ of weighted irreducible facet inducing Steiner graphs with at most $\tau$ terminals, depending on $\tau$ only, with the following properties.
--
--   1. Every irreducible facet inducing weighted Steiner graph with at most $\tau$ terminals is isomorphic to a member of $\mathcal F$.
--   2. A weighted Steiner graph with at most $\tau$ terminals is facet inducing if and only if it is constructable from $\mathcal F$ by subdivisions and gluings.
--   3. For every Steiner graph $(G,T)$ with $|T|\le\tau$, the non-trivial facet defining inequalities $ax\ge b$, $b>0$, of $\mathrm{CUT}_+(G,T)$ are exactly the positive multiples $r(c,\gamma_c)$ of the inequalities $cx\ge\gamma_c(G_a,T)$ of the weighted Steiner subgraphs $(G_a,T)$ constructable from $\mathcal F$.
--   4. $\mathrm{CUT}_+(G,T)$ consists of the nonnegative points satisfying these inequalities.
--
--   In the words of the abstract: for each integer $\tau$ there is a finite set of inequalities such that for every pair $(G,T)$ with $|T|\le\tau$ the non-trivial facet defining inequalities of $\mathrm{CUT}_+(G,T)$ are the inequalities that can be obtained via iterated applications of two simple operations, starting from that set.
--
--   **Formalization Note** $\mathcal F$ is chosen before the graph. Non-trivial means right-hand side $b>0$, by Remark 1 (1). `Constructable` is linear, as on p.10.
--
--   Differences from the source:
--   - reading: Main Result I, an informal statement citing Remark 3 and Theorem 4 → one theorem with the five clauses finiteness and irreducibility of F, completeness up to isomorphism, Remark 3 for F, the facets, and the description; reason: this is the conjunction of what the page cites and what its abstract claims, with one F for all graphs; p.3's "with τ terminals" is read as the abstract's |T| ≤ τ
--   - encoding: inequalities in minimum integer form → real (a, b) with a = r·c on the support and b = r·γ_c; reason: covers every scaling of the same inequality
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Main Result I, p.3; Theorem 4 and Remark 3, p.11; Remarks 1–2, pp.4–5

import Mathlib
import Definitions.Def_SteinerCutDominants_DefinesFacet
import Definitions.Def_SteinerCutDominants_IsIrreducible
import Definitions.Def_SteinerCutDominants_Constructable
import Definitions.Def_SteinerCutDominants_IsSupportRep

open Matrix

namespace SteinerCutDominants

/-- **Main Result I** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.3, with
Theorem 4 and Remark 3, p.11, and Remarks 1–2, pp.4–5). For each `τ` there is a finite family `F` of
weighted irreducible facet inducing Steiner graphs, with at most `τ` terminals, chosen before the
graph, such that for every Steiner graph with at most `τ` terminals: (a)–(b) `F` contains every
irreducible one up to isomorphism; (c) a weighted Steiner graph is facet inducing iff it is
constructable from `F`; (d) the non-trivial facet defining inequalities of `CUT₊(G, T)` are the
scaled weights of the constructable Steiner subgraphs; (e) those inequalities, with the
nonnegativity constraints, describe `CUT₊(G, T)`.

**Formalization Note** Non-trivial means right-hand side `b > 0` (Remark 1 (1)). Facet inequalities
are real vectors `a`; `H`, `φ`, `r` exhibit `a` as `r` times weights in minimum integer form on its
support graph. `Constructable` is linear, as on p.10. -/
theorem main_result_I (τ : ℕ) :
    ∃ F : Set WSG, F.Finite ∧
      (∀ H ∈ F, IsIrreducible H ∧ H.T.card ≤ τ) ∧
      (∀ H : WSG, IsIrreducible H → H.T.card ≤ τ → ∃ H₀ ∈ F, WSG.Iso H₀ H) ∧
      (∀ H : WSG, H.T.card ≤ τ → (IsFacetInducing H ↔ Constructable F H)) ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (T : Finset V), G.Connected → 2 ≤ T.card → T.card ≤ τ →
        ∀ (a : G.edgeSet → ℝ) (b : ℝ), 0 < b →
          (DefinesFacet G T a b ↔
            ∃ (H : WSG) (φ : H.V ↪ V) (r : ℝ), 0 < r ∧ IsSupportRep G T a H φ r ∧
              b = r * gamma H ∧ Constructable F H)) ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (T : Finset V), G.Connected → 2 ≤ T.card → T.card ≤ τ →
        cutDominant G T =
          {x | 0 ≤ x ∧
            ∀ (a : G.edgeSet → ℝ) (b : ℝ), 0 < b → DefinesFacet G T a b → b ≤ a ⬝ᵥ x}) := by sorry

end SteinerCutDominants
