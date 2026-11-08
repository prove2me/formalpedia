-- Prove2me | Theorems.Thm_PoSUndirected_theorem_3_1_pos_lower_bound
-- name    : PoSUndirected.theorem_3_1_pos_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:38.418692+00:00
-- url     : https://prove2.me/theorems/c854d9ae-81f3-4d84-8718-9a5383bc5cbf
-- title:
--   Theorem 3.1 — owned-edge games with a unique weak equilibrium and price of stability above $L-\varepsilon$, $L=7808358178989/3195649632469$
-- statement:
--   For every real $\varepsilon>0$ there is a finite undirected network design game with positive rational edge costs, one player for every edge, and all simple paths available to every player, such that its unique weak Nash equilibrium is the profile in which each player uses her own edge, and
--   $$
--   \mathrm{PoS}>L-\varepsilon,\qquad L=\frac{7808358178989}{3195649632469}=2.44343375433\ldots
--   $$
--
--   Concretely: there are a finite loopless multigraph $(V,E)$ and costs $c_e\in\mathbb Q$, $c_e>0$, such that in the owned-edge game (player $e$ chooses any simple path between the endpoints of $e$, edge costs shared equally among users) a profile $A$ is a weak Nash equilibrium if and only if $A_e=\{e\}$ for every $e$, and $C(\text{all-direct})>(L-\varepsilon)\,C(P)$ for every profile $P$.
--
--   This improves the general lower bound on the ordinary price of stability of undirected network design games with equal cost sharing from $348/155\approx2.24516$ (Bilò, Caragiannis, Fanelli and Monaco); the general upper bound remains logarithmic in the number of players.
--
--   **Formalization Note** The weak equilibrium is `IsPureNash` (no strictly improving unilateral move; ties allowed).
--
--   Differences from the source:
--   - encoding: $\mathrm{PoS}=\min_{N}C(N)/\mathrm{OPT}>L-\varepsilon$ → $(L-\varepsilon)\,C(P)<C(\text{all-direct})$ for every profile $P$; reason: the all-direct profile is the unique equilibrium and $\mathrm{OPT}$ is a minimum over finitely many profiles, so the two are equivalent (and both force $\mathrm{OPT}>0$)
--   - encoding: a finite undirected (multi)graph → finite types $V,E$ with an endpoint pair in `Sym2 V` for each edge and no loop; reason: the §2 model is a finite loopless multigraph
--   - encoding: "one player for every edge, and all simple paths available" → the owned-edge game, whose players are the edges and whose strategies are the edge sets of all simple paths between each edge's endpoints; reason: definition of endpoint ownership (§2)
--   - encoding: "its unique weak Nash equilibrium is the all-direct profile" → a profile is a weak equilibrium if and only if it is the all-direct profile; reason: existence and uniqueness
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorem 3.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_PoSUndirected_ndGame

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis, *The Price of Stability in Undirected Network Design: Lower Bounds and Structural
Guarantees* (preprint, sha256 c095d811…), Theorem 3.1, p.3 (PDF p.5). For every real `ε > 0` there
is a finite undirected network design game with positive rational edge costs, one player for
every edge, and all simple paths available to every player (the owned-edge game on a finite
loopless multigraph), such that its unique weak Nash equilibrium is the profile in which each
player uses her own edge, and `PoS > L − ε` with `L = 7808358178989/3195649632469`.

**Formalization Note.** The game is `ownerGame ends c` on finite types `V` (vertices) and `E`
(edges = players). `IsPureNash` is the weak equilibrium (ties allowed); the equivalence states
existence and uniqueness. Since the all-direct profile is the unique equilibrium and `OPT` is a
minimum over the finitely many profiles, `PoS = C(direct)/OPT > L − ε` is stated as
`(L − ε)·C(P) < C(direct)` for every profile `P`. -/
theorem theorem_3_1_pos_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype E) (_ : DecidableEq E)
      (ends : E → Sym2 V) (c : E → ℚ),
      (∀ e, ¬ (ends e).IsDiag) ∧ (∀ e, 0 < c e) ∧
      (∀ A : E → Finset E,
        IsPureNash (ownerGame ends (fun e => (c e : ℝ))) A ↔ A = fun e => {e}) ∧
      ∀ P : E → Finset E, IsProfile (ownerGame ends (fun e => (c e : ℝ))) P →
        ((7808358178989 / 3195649632469 : ℝ) - ε) * designCost (fun e _ => (c e : ℝ)) P <
          designCost (fun e _ => (c e : ℝ)) (fun e => {e}) := by sorry

end PoSUndirected
