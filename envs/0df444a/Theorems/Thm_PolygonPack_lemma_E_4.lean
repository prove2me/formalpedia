-- Prove2me | Theorems.Thm_PolygonPack_lemma_E_4
-- name    : PolygonPack.lemma_E_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:37.045305+00:00
-- url     : https://prove2.me/theorems/cf6428db-16bc-49ca-b7d7-d8c562399a29
-- title:
--   Lemma E.4 — the exceptional knapsack candidate
-- statement:
--   Let $c,a_0$ be rational with $0<c\le1/400$, $a_0>0$, and let $h_0=2a_0$ satisfy $h_0\le\min\{c/400,\,1/(500K),\,1/(300LK),\,1/16\}$. A polynomial-time machine returns on every valid instance a sound packing of polygons of $J=\mathrm{Large}\cup T^0$ whose profit is at least $\pi(S')$ for every feasible $S'\subseteq J$.
--
--   So the machine recovers a maximum-profit feasible subset of $J$, whose profit is at least $\pi(\mathrm{OPT}\cap J)$, since a subset of a feasible set is feasible.
--
--   Differences from the source:
--   - reading: J = Large ∪ T0, with fixed parameters → rational c, a0 under the cutoffs of Corollary A.6; reason: p.47 for rationality; the proof uses the corollary
--   - encoding: its profit is at least π(OPT ∩ J) → the bound for every feasible S' ⊆ J; reason: OPT ∩ J is one such S'
--   - reading: polynomial time in the total binary encoding length → Nonempty (Turing.TM2ComputableInPolyTime …) on the fixed binary encoders; reason: p.13 names this measure; the paper fixes no machine model
--   - reading: placements returned as exact real algebraic numbers of polynomial description length → each pose number as a nonzero integer polynomial with a rational interval isolating its root; reason: the per-coordinate form of p.48; description length follows from the time bound
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - reading: convex polygons (p.1) → polygons of positive area; reason: the paper assumes positive area on p.46; the degenerate extension there is optional
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma E.4, p.48

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_diag
import Definitions.Def_PolygonPack_eucl
import Definitions.Def_PolygonPack_thick
import Definitions.Def_PolygonPack_diamPair
import Definitions.Def_PolygonPack_polyArea
import Definitions.Def_PolygonPack_placedUV
import Definitions.Def_PolygonPack_canonBottom
import Definitions.Def_PolygonPack_IsTight
import Definitions.Def_PolygonPack_Kc
import Definitions.Def_PolygonPack_AlgNum
import Definitions.Def_PolygonPack_Out
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_encOut

namespace PolygonPack

/-- **Lemma E.4 (The exceptional knapsack candidate).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.48. "For J = Large ∪ T0, a maximum-profit feasible subset of J can be recovered exactly in polynomial bit time. In particular, its profit is at
least π(OPT ∩ J)."

For rational `c`, `a0` under the cutoffs of Corollary A.6, a machine returns a sound packing of polygons of `J` whose profit is at least that of every feasible subset of `J`. That is a maximum, and `π(OPT ∩ J)` is
the case `S' = OPT ∩ J`, since a subset of a feasible set is feasible.

**Formalization Note.** `c`, `a0` are rational because the classification is exact (p.47). The proof bounds the size of `J`'s feasible subsets by `⌊1/a0⌋ + 2`, using those cutoffs. -/
theorem lemma_E_4 (c a0 : ℚ) (hc : 0 < c) (hc' : c ≤ 1 / 400) (ha0 : 0 < a0) (hcut : IsA5Cutoff c (2 * a0)) :
    ∃ f : Instance → Out, Nonempty (Turing.TM2ComputableInPolyTime encInstance encOut f) ∧
      ∀ I : Instance, I.Valid → (f I).Sound I ∧
        (∀ i ∈ (f I).indexSet I, IsLarge a0 (I.verts i) ∨ IsTZero c a0 (I.verts i)) ∧
        ∀ S' : Finset (Fin I.n), Feasible I S' → (∀ i ∈ S', IsLarge a0 (I.verts i) ∨ IsTZero c a0 (I.verts i)) →
          profit I S' ≤ profit I ((f I).indexSet I) := by sorry

end PolygonPack
