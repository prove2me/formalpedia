-- Prove2me | Theorems.Thm_PoSUndirected_Supplement_theorem_5_3
-- name    : PoSUndirected.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:36:39.377223+00:00
-- url     : https://prove2.me/theorems/e38a1b8b-f5ad-4834-9cfb-36d1fb97c3e0
-- title:
--   Theorem 5.3 — routing singleton demands, $\mathrm{PoS}<761/385<2$
-- statement:
--   Partition the independently labelled players into maximal classes with the same unordered terminal pair, and let $D_{\mathrm{rep}}$ have one abstract edge for every class of size at least two. Suppose every singleton terminal pair has a path in $D_{\mathrm{rep}}$ and those abstract paths are pairwise edge-disjoint. Suppose also that one optimum forest profile has native load at most eight on each forest edge that is not a bridge of the full physical host. Then
--   $$
--   \mathrm{PoS}<\frac{761}{385}<2.
--   $$
--   There is no hypothesis on the physical host's cycle rank and no bound on the number of singleton players; their induced physical routes may overlap.
--
--   Differences from the source:
--   - encoding: one abstract edge per maximal repeated-demand class → the least-labelled member is used as the class representative; reason: gives a finite edge type canonically and does not alter the demand multigraph or its routing property
--   - encoding: $\mathrm{PoS}<761/385$ under the standing $\mathrm{OPT}>0$ convention → an attained optimum and cheapest equilibrium with positive optimum and the two strict cost inequalities; reason: equivalent for a finite game and avoids totalized division
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorem 5.3, p.12 (PDF p.14); proof, pp.63–64 (PDF pp.65–66)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_HasSingletonRouting

open CongestionPoA.AsymSum

set_option autoImplicit false

namespace PoSUndirected.Supplement

/-- **Theorem 5.3 (routing singleton demands).** Tsoufis, preprint sha256 c095d811…,
p.12 (PDF p.14); proof pp.63–64 (PDF pp.65–66).

If singleton demand classes have pairwise edge-disjoint abstract routes in `D_rep`, and one
optimum forest has native load at most eight on every forest edge that is not a bridge of the full
physical host, then ordinary PoS is strictly below `761/385`, hence below two.

**Formalization Note.** `HasSingletonRouting` concerns abstract repeated-class edges; it imposes no
disjointness on physical paths.  No maximum-block-rank hypothesis and no bound on the number of
singleton players occurs below.  Host bridges are expressly excluded from the native-load cap. -/
theorem theorem_5_3 {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] (ends : E → Sym2 V) (c : E → ℝ)
    (s t : ι → V) (hloop : IsLoopless ends) (hcost : ∀ e, 0 < c e)
    (hnontrivial : ∀ i, s i ≠ t i)
    (hroute : HasSingletonRouting s t) (hcap : HasCappedOptimumForest ends c s t)
    (hopt : ∃ O : ι → Finset E,
      IsSocialOptimum (ndGame ends c s t) c O ∧ 0 < socialCost c O) :
    ∃ (O N : ι → Finset E),
      IsSocialOptimum (ndGame ends c s t) c O ∧
      IsCheapestEquilibrium (ndGame ends c s t) c N ∧
      0 < socialCost c O ∧
      socialCost c N < ((761 : ℝ) / 385) * socialCost c O ∧
      socialCost c N < 2 * socialCost c O := by sorry

end PoSUndirected.Supplement
