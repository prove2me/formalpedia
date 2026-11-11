-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_lemma_5_2
-- name    : PatternRangeCounting1593.RangeCounting.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:51.605835+00:00
-- url     : https://prove2.me/theorems/2e7a51fe-da9c-46c5-9b6c-89f23443a4fb
-- title:
--   Lemma 5.2 — constant-time state refinement
-- statement:
--   Fix $\pi$ with $|\pi|\ge3$, $K\ge2$, retained operation programs with step bound $T$ and a navigation program with step bound $T_{nav}$. There are an absolute constant $c$ and a fixed program such that, above a threshold, for every $\pi$-avoiding $\tau$ of length $m$, admissible $w$, retained representation and navigation structure: if $Z=C_0\times R_0$ is an occupied cell at a level $i<\ell$ containing the query corner $(x,y)$, then from the handles of $C_0$ and $R_0$ and the state $(p,c,d)=(p(Z),c(Z),d(Z))$ the program returns within $c(T+T_{nav}+1)$ steps, for the child $E=C\times R$ of $Z$ containing $(x,y)$: the handles of $C$ and $R$, whether $E$ is occupied, and $(p(E),c(E),d(E))$.
--
--   Repeating this step reaches the terminal cell of the query in a constant number of steps.
--
--   Differences from the source:
--   - generalization: deterministic word RAM with w = Θ(log N) and constant-time standard operations including multiplication and most-significant-bit → the explicit instruction set of Def_Machine (one step per instruction, no division) at every width 2·b(N) ≤ w ≤ K·b(N) for a fixed K ≥ 2, N = max{2, n}; reason: uniformity over each fixed bounded width band; choosing K = 2 and w = 2·b(max{2,n}) recovers one legal logarithmic width rule sufficient for coordinate pairs, so every source instance is covered
--   - encoding: in O(1) time → within c·(T+T_nav+1) steps, c absolute; reason: a constant number of navigation and local-counter calls
--   - encoding: occupancy → 1 if E is occupied, 0 otherwise, in an output register; reason: Boolean as a word
--   - generalization: the retained programs and navigation structures used in Sections 4–5 → any fixed programs satisfying the stated retained and navigation contracts, with constants and thresholds allowed to depend on these fixed programs; reason: the source implementations satisfy these contracts; specializing to them gives the complete source result
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 5.2, printed p. 18 (PDF p. 19), proof printed pp. 18–19

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy
import Definitions.Def_PatternRangeCounting1593_RangeCounting_KOInterface
import Definitions.Def_PatternRangeCounting1593_RangeCounting_IndexSpecs
set_option autoImplicit false
open Filter Topology
open Classical

namespace PatternRangeCounting1593.RangeCounting

/-- Lemma 5.2 (Constant-time state refinement). -/
theorem lemma_5_2 :
    ∃ c : ℕ, ∀ (k : ℕ) (π : Equiv.Perm (Fin k)), 3 ≤ k → ∀ K : ℕ, 2 ≤ K →
      ∀ (P : KOProgs) (T cKO : ℕ) (navP : Program) (Tnav : ℕ),
      ∃ (refP : Program) (m₀ : ℕ),
        ∀ m ≥ m₀, ∀ τ : Equiv.Perm (Fin m), Avoids π τ → ∀ w, WidthOK K m w →
          ∀ (base N : List Bool) (Hd : Hierarchy) (hdl : Handles),
            KOInterface π w τ P T cKO base Hd hdl → NavSpec w τ navP Tnav base N Hd hdl →
            ∀ (buf : List Bool) (oN : ℕ), base <+: buf → SliceAt buf oN N →
              buf.length < 2 ^ w →
            ∀ x y i, 1 ≤ x → x ≤ m → 1 ≤ y → y ≤ m → i < Hd.ell →
              occ (colView τ Hd) i (Hd.cb i x) (Hd.rb i y) →
              RunsQueryRO w refP (packBits w buf)
                [m, oN, x, y, i,
                 hdl.node 0 i (Hd.cb i x), hdl.addr 0 i (Hd.cb i x),
                 hdl.node 1 i (Hd.rb i y), hdl.addr 1 i (Hd.rb i y),
                 nwCount (colView τ Hd) i (Hd.cb i x) (Hd.rb i y),
                 cutAbove (colView τ Hd) i (Hd.cb i x) (Hd.rb i y),
                 cutAbove (rowView τ Hd) i (Hd.rb i y) (Hd.cb i x)]
                [hdl.node 0 (i + 1) (Hd.cb (i + 1) x), hdl.addr 0 (i + 1) (Hd.cb (i + 1) x),
                 hdl.node 1 (i + 1) (Hd.rb (i + 1) y), hdl.addr 1 (i + 1) (Hd.rb (i + 1) y),
                 if occ (colView τ Hd) (i + 1) (Hd.cb (i + 1) x) (Hd.rb (i + 1) y) then 1 else 0,
                 nwCount (colView τ Hd) (i + 1) (Hd.cb (i + 1) x) (Hd.rb (i + 1) y),
                 cutAbove (colView τ Hd) (i + 1) (Hd.cb (i + 1) x) (Hd.rb (i + 1) y),
                 cutAbove (rowView τ Hd) (i + 1) (Hd.rb (i + 1) y) (Hd.cb (i + 1) x)]
                (c * (T + Tnav + 1)) := by sorry

end PatternRangeCounting1593.RangeCounting
