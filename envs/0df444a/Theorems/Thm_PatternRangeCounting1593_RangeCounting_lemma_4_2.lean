-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_lemma_4_2
-- name    : PatternRangeCounting1593.RangeCounting.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:08.95361+00:00
-- url     : https://prove2.me/theorems/ca8be3fc-0141-49dc-93a6-f2d5a5b3434c
-- title:
--   Lemma 4.2 — navigation from an anchor
-- statement:
--   Fix $\pi$ with $|\pi|\ge3$, a width parameter $K\ge2$ and any retained Kozma–Opler operation programs with step bound $T$. There are an absolute constant $c$, a fixed program and a constant $C$ such that, above a threshold, for every $\pi$-avoiding $\tau$ of length $m$, every admissible $w$ and every retained Kozma–Opler representation $\beta$ of $\tau$ (hierarchy and handles as in Theorem 3.4), there is a bit string $N$ (the directories, degree arrays and ancestor records) with
--   $$|N|\le C\bigl(H+m_a\,\ell\,\log_2 m\bigr),\qquad \frac{H+m_a\ell\log_2 m}{m}\to0,$$
--   such that, given a coordinate $x$ on either axis and a level $i\le\ell$, the program returns within $c(T+1)$ steps the handle of the level-$i$ block containing $x$ (node identifier and local-counter address), its index at level $i$, its first coordinate and degree, its width when $i=\ell$, and its one-based child index within its parent. Here $m_a$ is the number of anchor blocks per axis and $\ell$ the depth.
--
--   The lemma lets every later step address any block on the path of a query coordinate in constant time.
--
--   Differences from the source:
--   - generalization: deterministic word RAM with w = Θ(log N) and constant-time standard operations including multiplication and most-significant-bit → the explicit instruction set of Def_Machine (one step per instruction, no division) at every width 2·b(N) ≤ w ≤ K·b(N) for a fixed K ≥ 2, N = max{2, n}; reason: uniformity over each fixed bounded width band; choosing K = 2 and w = 2·b(max{2,n}) recovers one legal logarithmic width rule sufficient for coordinate pairs, so every source instance is covered
--   - reading: they recover its block at any specified level … and the required child ranks → the block's handle and its zero-based index at that level; the one-based child index within its parent; reason: the proof identifies blocks by handle and by rank (anchor rank, finest rank) and uses one-based child indices in Lemma 5.2
--   - encoding: in O(1) time → within c·(T+1) steps, c absolute, T the step bound of the retained operations; reason: the structure calls a constant number of retained operations
--   - encoding: O_π(H + m_a ℓ log m) = o_π(m) bits → |N| ≤ C·(H + m_a ℓ log₂ m) above the threshold and (H + m_a ℓ log₂ m)/m → 0; reason: standard reading of O and o
--   - encoding: these directories, degree arrays, and ancestor records → a bit string N at any bit offset of a buffer beginning with the retained representation, read-only, offset in a register; reason: composable layout
--   - generalization: the retained programs and navigation structures used in Sections 4–5 → any fixed programs satisfying the stated retained and navigation contracts, with constants and thresholds allowed to depend on these fixed programs; reason: the source implementations satisfy these contracts; specializing to them gives the complete source result
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 4.2, printed p. 15 (PDF p. 16)

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

/-- Lemma 4.2 (Navigation from an anchor). -/
theorem lemma_4_2 :
    ∃ c : ℕ, ∀ (k : ℕ) (π : Equiv.Perm (Fin k)), 3 ≤ k → ∀ K : ℕ, 2 ≤ K →
      ∀ (P : KOProgs) (T cKO : ℕ),
      ∃ (navP : Program) (C : ℝ) (m₀ : ℕ),
        Tendsto (fun m : ℕ => ((Hsum m : ℝ) +
            blocksAt m (anchorLevel m) * depth m * Real.logb 2 m) / m) atTop (𝓝 0) ∧
        ∀ m ≥ m₀, ∀ τ : Equiv.Perm (Fin m), Avoids π τ → ∀ w, WidthOK K m w →
          ∀ (base : List Bool) (Hd : Hierarchy) (hdl : Handles),
            KOInterface π w τ P T cKO base Hd hdl →
            ∃ N : List Bool,
              (N.length : ℝ) ≤
                C * ((Hsum m : ℝ) + blocksAt m (anchorLevel m) * depth m * Real.logb 2 m) ∧
              NavSpec w τ navP (c * (T + 1)) base N Hd hdl := by sorry

end PatternRangeCounting1593.RangeCounting
