-- Prove2me | Theorems.Thm_WeightedCongestionBR_theorem_5
-- name    : WeightedCongestionBR.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:22.286458+00:00
-- url     : https://prove2.me/theorems/163d9857-d82b-47c5-a998-8a1144791ee6
-- title:
--   Theorem 5 — a fixed player's cost and deviations change little, (16) and (17)
-- statement:
--   Throughout, $\Gamma$ is a weighted polynomial congestion game of degree $d\ge1$ with weights $w_u\ge1$, $s_{\mathrm{init}}$ is an initial state with $c_{\min}>0$, and $m\ge1$ is an integer with $c_{\max}/c_{\min}\le g^m$ (Algorithm 1's parameters). Suppose the strategy of player $u$ was fixed at the end of phase $j$ (by Line 11, or by Line 12 after the last phase). Then for the final state $s^{m-1}$,
--
--   $$
--   C_u(s^{m-1})\le(1+3p^{-1})\,C_u(s^j)\tag{16}
--   $$
--
--   and
--
--   $$
--   C_u(s^{m-1}_{-u},s'_u)\ge(1-2p^{-1})\,C_u(s^j_{-u},s'_u)\qquad\text{for all }s'_u\in S_u.\tag{17}
--   $$
--
--   With the absence of $p$-moves at $s^j$ it gives Theorem 6.
--
--   Differences from the source:
--   - encoding: s^j and s^{m−1} of one execution → configurations cj (after the end of phase j, state s^j) and cf (phase m, state s^{m−1}) with cj reachable and cf reachable from cj; reason: a run through cj that continues to cf is one execution; the end-of-phase step does not change the state
--   - generalization: m = log(c_max/c_min) (Line 1) → any integer m ≥ 1 with c_max/c_min ≤ g^m, g computed from m; reason: Reading 2: Line 1's m must be an integer; ⌈log(c_max/c_min)⌉ clamped to 1 is one such m, and the proof uses only m ≥ 1 and b_m ≤ c_min
--   - encoding: c_min used as a divisor in Line 1 → hypothesis 0 < c_min; reason: Reading 3: with c_min = 0 the value m = log(c_max/0) is undefined; the hypothesis excludes only those undefined cases
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
--   - encoding: the strategy of u was fixed at the end of phase j → u enters N_fixed in the end-of-phase step cprev → cj (Line 11), or cj is in phase m, u ∉ N_fixed and C_u(s^{m−1}) ≥ b_m (Line 12, j = m − 1); reason: these are the two lines of Algorithm 1 that fix a player; phase 0 fixes nobody
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 5, p.19 (proof pp.20–21)

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_alphaC
import Definitions.Def_WeightedCongestionBR_pConst
import Definitions.Def_WeightedCongestionBR_cmax
import Definitions.Def_WeightedCongestionBR_cmin
import Definitions.Def_WeightedCongestionBR_gConst
import Definitions.Def_WeightedCongestionBR_bnd
import Definitions.Def_WeightedCongestionBR_Config
import Definitions.Def_WeightedCongestionBR_AlgStep
import Definitions.Def_WeightedCongestionBR_Reach
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Theorem 5** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.19). Suppose the strategy of player `u` was fixed at the end of phase `j`.
Then `C_u(s^{m−1}) ≤ (1 + 3p⁻¹) C_u(s^j)` (16) and
`C_u(s^{m−1}_{-u}, s'_u) ≥ (1 − 2p⁻¹) C_u(s^j_{-u}, s'_u)` for all `s'_u ∈ S_u` (17).

**Formalization Note** Along one run: `cprev` is reachable, the end-of-phase step of phase
`j = cprev.phase` leads to `cj` (so `cj.s = s^j`), and `cf`, reached from `cj`, is in phase `m` (so
`cf.s = s^{m−1}`, the output). "`u` fixed at the end of phase `j`" is either Line 11 (`u` enters
`N_fixed` in that step) or Line 12 (`j = m − 1`, `u ∉ N_fixed` and `C_u(s^{m−1}) ≥ b_m`). Hypotheses of
Algorithm 1 as in `theorem_3`. -/
theorem theorem_5 {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u) (hm : 1 ≤ m)
    (hcmin : 0 < cmin G) (hratio : cmax G sinit / cmin G ≤ gConst n d m ^ m)
    (cprev cj cf : Config G) (hprev : Reach G d m sinit cprev) (hstep : AlgStep G d m sinit cprev cj)
    (hend : cj.phase = cprev.phase + 1) (hcf : Relation.ReflTransGen (AlgStep G d m sinit) cj cf)
    (hfm : cf.phase = m) (u : Fin n)
    (hfix : (u ∉ cprev.F ∧ u ∈ cj.F) ∨
      (cj.phase = m ∧ u ∉ cj.F ∧ bnd G d m sinit m ≤ privateCost G cj.s u)) :
    privateCost G cf.s u ≤ (1 + 3 / pConst d) * privateCost G cj.s u ∧
      ∀ t : G.Strategy u,
        (1 - 2 / pConst d) * privateCost G (Function.update cj.s u t) u ≤
          privateCost G (Function.update cf.s u t) u := by sorry

end WeightedCongestionBR
