-- Prove2me | Theorems.Thm_PolygonPack_theorem_C_9
-- name    : PolygonPack.theorem_C_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:02.367184+00:00
-- url     : https://prove2.me/theorems/bd5b152a-bd13-41a6-8e23-4730b52126be
-- title:
--   Theorem C.9 — the elongated packing
-- statement:
--   For every $\varepsilon_E>0$ there are a rational $c$ with $0<c\le1/400$ and a cutoff $\bar a>0$ such that, for every rational $a_0$ with $0<a_0\le\bar a$, a polynomial-time machine returns on every valid instance a sound packing of polygons of $T^+\cup\mathrm{Slack}$, of profit $V$, with
--   $$
--   \pi(S')\le(R+\varepsilon_E)\,V,\qquad R=2+2\sqrt2,
--   $$
--   for every feasible $S'\subseteq T^+\cup\mathrm{Slack}$. Equivalently, $V\ge(W_{T^+}+W_{\mathrm{Slack}})/(R+\varepsilon_E)$ for every feasible comparison packing.
--
--   This is the candidate for elongated polygons in the final algorithm.
--
--   Differences from the source:
--   - reading: for every fixed ε_E > 0, the algorithm constructs a packing → ∃ rational c, ∃ cutoff, ∀ rational a0 up to it, ∃ machine; reason: the order of App. F.2, p.51, "All these upper bounds are positive", rational by p.47
--   - encoding: W_{T+} + W_Slack in an arbitrary feasible comparison packing → S' feasible with all members in T+ ∪ Slack; reason: the class part of a feasible packing is feasible, and conversely
--   - reading: polynomial time in the total binary encoding length → Nonempty (Turing.TM2ComputableInPolyTime …) on the fixed binary encoders; reason: p.13 names this measure; the paper fixes no machine model
--   - reading: placements returned as exact real algebraic numbers of polynomial description length → each pose number as a nonzero integer polynomial with a rational interval isolating its root; reason: the per-coordinate form of p.48; description length follows from the time bound
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - reading: convex polygons (p.1) → polygons of positive area; reason: the paper assumes positive area on p.46; the degenerate extension there is optional
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem C.9, p.39; proof, pp.39–40; App. F.2, p.51

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
import Definitions.Def_PolygonPack_clearance

namespace PolygonPack

/-- **Theorem C.9 (The elongated packing).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.39. "For every fixed ε_E > 0, the algorithm constructs a packing of profit at least (W_{T+} + W_Slack)/(R + ε_E), where W_{T+} and
W_Slack are the profits of positive-Tight and Slack polygons, respectively, in an arbitrary feasible comparison packing."

"The algorithm" is the polynomial-time construction of the proof on pp.39–40. For `ε_E > 0` it fixes a rational `c ≤ 1/400` and a cutoff `ā`, and for every rational `a0 ≤ ā` a machine returns a
sound packing of `T+ ∪ Slack` polygons with the bound against every feasible subset of `T+ ∪ Slack`.

**Formalization Note.** The order `ε_E → c → ā → a0` records App. F.2 (p.51): "All these upper bounds are positive", so every smaller `a0` also works, and the goal can use one common `a0` for all
candidates. `c` and `a0` are rational because a machine compares with them exactly (p.47). The comparison family `S'` is any feasible subset of the class. -/
theorem theorem_C_9 (εE : ℝ) (hεE : 0 < εE) :
    ∃ c : ℚ, 0 < c ∧ c ≤ 1 / 400 ∧ ∃ abar : ℝ, 0 < abar ∧ ∀ a0 : ℚ, 0 < a0 → (a0 : ℝ) ≤ abar →
      ∃ f : Instance → Out, Nonempty (Turing.TM2ComputableInPolyTime encInstance encOut f) ∧
        ∀ I : Instance, I.Valid → (f I).Sound I ∧
          (∀ i ∈ (f I).indexSet I, IsTPlus c a0 (I.verts i) ∨ IsSlack c a0 (I.verts i)) ∧
          ∀ S' : Finset (Fin I.n), Feasible I S' → (∀ i ∈ S', IsTPlus c a0 (I.verts i) ∨ IsSlack c a0 (I.verts i)) →
            profit I S' ≤ (constR + εE) * profit I ((f I).indexSet I) := by sorry

end PolygonPack
