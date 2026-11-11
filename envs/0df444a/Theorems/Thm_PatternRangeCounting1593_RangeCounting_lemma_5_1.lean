-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_lemma_5_1
-- name    : PatternRangeCounting1593.RangeCounting.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:25.106365+00:00
-- url     : https://prove2.me/theorems/f1c2b561-66ce-4451-ab1e-a01581e2ec71
-- title:
--   Lemma 5.1 — boundary continuation
-- statement:
--   Fix $\pi$ with $|\pi|\ge3$, $K\ge2$, retained operation programs with step bound $T$ and a navigation program with step bound $T_{nav}$. There are an absolute constant $c$, fixed query and construction programs, a constant $C$ and a function $e$ with $e(m)/m\to0$ such that, above a threshold, for every $\pi$-avoiding $\tau$ of length $m$, admissible $w$, retained representation and navigation structure: the construction program, started on a buffer holding them together with the occupied-cell lists, halts within $e(m)$ steps with a bit string $J$ of
--   $$|J|\le C\bigl(m_a\ell\log_2 m+L\log_2\log_2 m\bigr),\qquad\frac{m_a\ell\log_2 m+L\log_2\log_2 m}{m}\to0$$
--   bits, and the query program evaluates $G_B(x,c)$ for every block $B$ of either axis at every level (given by its handle), every cut $0\le c\le\deg(B)$ and every $\min B-1\le x\le\max B$, within $c(T+T_{nav}+1)$ steps.
--
--   These boundary prefixes are the two strip contributions of the four-region identity at the terminal cell.
--
--   Differences from the source:
--   - generalization: deterministic word RAM with w = Θ(log N) and constant-time standard operations including multiplication and most-significant-bit → the explicit instruction set of Def_Machine (one step per instruction, no division) at every width 2·b(N) ≤ w ≤ K·b(N) for a fixed K ≥ 2, N = max{2, n}; reason: uniformity over each fixed bounded width band; choosing K = 2 and w = 2·b(max{2,n}) recovers one legal logarithmic width rule sufficient for coordinate pairs, so every source instance is covered
--   - encoding: supports G_C and G_R in O(1) time → one program with an axis input, within c·(T+T_nav+1) steps, c absolute; reason: row-block case is the transposed view
--   - encoding: given the occupied-cell lists and the retained counter … constructible in o_π(m) time → a construction program on memory holding the packed buffer and the occupied-cell lists as words, within e(m) steps, e(m)/m → 0; reason: explicit input layout
--   - generalization: the retained programs and navigation structures used in Sections 4–5 → any fixed programs satisfying the stated retained and navigation contracts, with constants and thresholds allowed to depend on these fixed programs; reason: the source implementations satisfy these contracts; specializing to them gives the complete source result
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 5.1, printed p. 17 (PDF p. 18); construction in §7.1, printed p. 24 (PDF p. 25)

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

/-- Lemma 5.1 (Boundary continuation). -/
theorem lemma_5_1 :
    ∃ c : ℕ, ∀ (k : ℕ) (π : Equiv.Perm (Fin k)), 3 ≤ k → ∀ K : ℕ, 2 ≤ K →
      ∀ (P : KOProgs) (T cKO : ℕ) (navP : Program) (Tnav : ℕ),
      ∃ (bdP build : Program) (C : ℝ) (m₀ : ℕ) (e : ℕ → ℝ),
        Tendsto (fun m : ℕ => ((blocksAt m (anchorLevel m) : ℝ) * depth m * Real.logb 2 m +
            finestCount m * Real.logb 2 (Real.logb 2 m)) / m) atTop (𝓝 0) ∧
        Tendsto (fun m : ℕ => e m / m) atTop (𝓝 0) ∧
        ∀ m ≥ m₀, ∀ τ : Equiv.Perm (Fin m), Avoids π τ → ∀ w, WidthOK K m w →
          ∀ (base N : List Bool) (Hd : Hierarchy) (hdl : Handles),
            KOInterface π w τ P T cKO base Hd hdl → NavSpec w τ navP Tnav base N Hd hdl →
            ∀ (buf : List Bool) (oN oL : ℕ), base <+: buf → SliceAt buf oN N →
              numWords w buf.length ≤ oL → oL + (occListWords τ Hd).length < 2 ^ w →
              ∃ (J : List Bool) (W : ℝ),
                BuildsWith w build (layoutMem w buf oL (occListWords τ Hd)) [m, oN, oL]
                  (e m) W J [] ∧
                (J.length : ℝ) ≤ C * ((blocksAt m (anchorLevel m) : ℝ) * depth m * Real.logb 2 m +
                  finestCount m * Real.logb 2 (Real.logb 2 m)) ∧
                BoundarySpec w τ bdP (c * (T + Tnav + 1)) base N J Hd hdl := by sorry

end PatternRangeCounting1593.RangeCounting
