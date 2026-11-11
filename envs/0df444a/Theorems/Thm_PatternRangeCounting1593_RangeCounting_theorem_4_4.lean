-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_theorem_4_4
-- name    : PatternRangeCounting1593.RangeCounting.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:11.478571+00:00
-- url     : https://prove2.me/theorems/e432341b-f5a3-446a-b9eb-ff75827145e3
-- title:
--   Theorem 4.4 — gateway search through the anchor
-- statement:
--   Fix $\pi$ with $|\pi|\ge3$, $K\ge2$, retained operation programs with step bound $T$, and a navigation program (Lemma 4.2) with step bound $T_{nav}$. There are an absolute constant $c$, fixed query and construction programs, a constant $C$ and a function $e$ with $e(m)/m\to0$ such that, above a threshold, for every $\pi$-avoiding $\tau$ of length $m$, admissible $w$, retained representation $\beta$ and navigation structure $N$: the construction program, started on a buffer holding $\beta$ and $N$ together with the occupied-cell lists, halts within $e(m)$ steps with a bit string $D$ satisfying
--   $$|D|\le C\,m_a\,\ell^2\log_2 m,\qquad \frac{m_a\ell^2\log_2 m}{m}\to0,$$
--   and, given $x,y\in[m]$, the query program returns within $c(T+T_{nav}+1)$ steps the largest $i^*\le a$ for which $Z=C_{i^*}(x)\times R_{i^*}(y)$ is occupied, together with $(p(Z),c(Z),d(Z))$.
--
--   The gateway index supplies the exact state of the deepest occupied containing cell through the anchor, from which the query descends.
--
--   Differences from the source:
--   - generalization: deterministic word RAM with w = Θ(log N) and constant-time standard operations including multiplication and most-significant-bit → the explicit instruction set of Def_Machine (one step per instruction, no division) at every width 2·b(N) ≤ w ≤ K·b(N) for a fixed K ≥ 2, N = max{2, n}; reason: uniformity over each fixed bounded width band; choosing K = 2 and w = 2·b(max{2,n}) recovers one legal logarithmic width rule sufficient for coordinate pairs, so every source instance is covered
--   - reading: an O_π(m_a ℓ² log m)-bit index returns … given x, y ∈ [m] → the index D is used together with the retained representation and the navigation structure of Lemma 4.2; reason: the proof takes the anchor ranks of x and y from Lemma 4.2's marker bitvectors, which are not part of D's budget
--   - encoding: in O(1) time → within c·(T+T_nav+1) steps, c absolute; reason: a constant number of retained and navigation operations plus one fusion-node search
--   - encoding: given the occupied-cell lists and the retained counter … constructible in o_π(m) time → a construction program on memory holding the packed buffer (with the retained representation and N) and the occupied-cell lists as words, halting within e(m) steps, e(m)/m → 0; reason: explicit input layout for the construction
--   - generalization: the retained programs and navigation structures used in Sections 4–5 → any fixed programs satisfying the stated retained and navigation contracts, with constants and thresholds allowed to depend on these fixed programs; reason: the source implementations satisfy these contracts; specializing to them gives the complete source result
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Theorem 4.4, printed p. 16 (PDF p. 17); construction in §7.1, printed pp. 24–25 (PDF pp. 25–26)

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

/-- Theorem 4.4 (Gateway search through the anchor). -/
theorem theorem_4_4 :
    ∃ c : ℕ, ∀ (k : ℕ) (π : Equiv.Perm (Fin k)), 3 ≤ k → ∀ K : ℕ, 2 ≤ K →
      ∀ (P : KOProgs) (T cKO : ℕ) (navP : Program) (Tnav : ℕ),
      ∃ (gwP build : Program) (C : ℝ) (m₀ : ℕ) (e : ℕ → ℝ),
        Tendsto (fun m : ℕ =>
          (blocksAt m (anchorLevel m) : ℝ) * depth m ^ 2 * Real.logb 2 m / m) atTop (𝓝 0) ∧
        Tendsto (fun m : ℕ => e m / m) atTop (𝓝 0) ∧
        ∀ m ≥ m₀, ∀ τ : Equiv.Perm (Fin m), Avoids π τ → ∀ w, WidthOK K m w →
          ∀ (base N : List Bool) (Hd : Hierarchy) (hdl : Handles),
            KOInterface π w τ P T cKO base Hd hdl → NavSpec w τ navP Tnav base N Hd hdl →
            ∀ (buf : List Bool) (oN oL : ℕ), base <+: buf → SliceAt buf oN N →
              numWords w buf.length ≤ oL → oL + (occListWords τ Hd).length < 2 ^ w →
              ∃ (D : List Bool) (W : ℝ),
                BuildsWith w build (layoutMem w buf oL (occListWords τ Hd)) [m, oN, oL]
                  (e m) W D [] ∧
                (D.length : ℝ) ≤
                  C * ((blocksAt m (anchorLevel m) : ℝ) * depth m ^ 2 * Real.logb 2 m) ∧
                GatewaySpec w τ gwP (c * (T + Tnav + 1)) base N D Hd := by sorry

end PatternRangeCounting1593.RangeCounting
