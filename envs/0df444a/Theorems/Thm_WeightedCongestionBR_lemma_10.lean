-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_10
-- name    : WeightedCongestionBR.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:30.475887+00:00
-- url     : https://prove2.me/theorems/41e640ba-c9e9-49d4-b175-6080e8a13af0
-- title:
--   Lemma 10 — cost drift of a fixed player during a later phase, (18) and (19)
-- statement:
--   Throughout, $\Gamma$ is a weighted polynomial congestion game of degree $d\ge1$ with weights $w_u\ge1$, $s_{\mathrm{init}}$ is an initial state with $c_{\min}>0$, and $m\ge1$ is an integer with $c_{\max}/c_{\min}\le g^m$ (Algorithm 1's parameters). Fix $\varepsilon>0$ and let $\xi_\varepsilon=(1+1/\varepsilon)^d d^d$. Let $u$ be a player whose strategy was fixed immediately after a phase $j$, and let $i>j$ be a later phase, from state $s^{i-1}$ to state $s^i$ with moving players $R_i$. Then
--
--   $$
--   C_u(s^i)\le(1+\varepsilon)\,C_u(s^{i-1})+\xi_\varepsilon\,\Phi_{R_i}(s^{i-1})\tag{18}
--   $$
--
--   and, for all $s'_u\in S_u$,
--
--   $$
--   C_u(s^i_{-u},s'_u)\ge\frac1{1+\varepsilon}\,C_u(s^{i-1}_{-u},s'_u)-\frac{\xi_\varepsilon}{1+\varepsilon}\,\Phi_{R_i}(s^{i-1}).\tag{19}
--   $$
--
--   Applied over the phases after $j$ it gives Theorem 5.
--
--   Differences from the source:
--   - encoding: u fixed immediately after a phase j, and a phase i > j → u ∈ N_fixed at the configuration where phase i begins; reason: N_fixed at the start of phase i consists exactly of the players fixed after phases 1, …, i − 1 (phase 0 fixes nobody)
--   - generalization: m = log(c_max/c_min) (Line 1) → any integer m ≥ 1 with c_max/c_min ≤ g^m, g computed from m; reason: Reading 2: Line 1's m must be an integer; ⌈log(c_max/c_min)⌉ clamped to 1 is one such m, and the proof uses only m ≥ 1 and b_m ≤ c_min
--   - encoding: c_min used as a divisor in Line 1 → hypothesis 0 < c_min; reason: Reading 3: with c_min = 0 the value m = log(c_max/0) is undefined; the hypothesis excludes only those undefined cases
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 10, p.20 (proof in Appendix C, pp.27–30)

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
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_cfgMovers
import Definitions.Def_WeightedCongestionBR_PhasePrefix
import Definitions.Def_WeightedCongestionBR_PhaseRun
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Lemma 10** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.20; proof in Appendix C, pp.27–30). Fix `ε > 0` and let
`ξ_ε := (1 + 1/ε)^d d^d`. For any player `u` whose strategy was fixed immediately after a phase `j`
and any phase `i > j`:
`C_u(s^i) ≤ (1 + ε) C_u(s^{i−1}) + ξ_ε Φ_{R_i}(s^{i−1})` (18) and
`C_u(s^i_{-u}, s'_u) ≥ (1/(1 + ε)) C_u(s^{i−1}_{-u}, s'_u) − (ξ_ε/(1 + ε)) Φ_{R_i}(s^{i−1})` for all
`s'_u ∈ S_u` (19).

**Formalization Note** Phase `i` is a complete phase `l` (`PhaseRun`) from a configuration `c` (state
`s^{i−1}`) to `cl` (state `s^i`), with movers `R_i = cfgMovers l`. "Fixed after some phase `j < i`" is
`u ∈ c.F`: `N_fixed` at the start of phase `i` holds exactly the players fixed after phases
`1, …, i − 1`. Hypotheses of Algorithm 1 as in `theorem_3`. -/
theorem lemma_10 {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u) (hm : 1 ≤ m)
    (hcmin : 0 < cmin G) (hratio : cmax G sinit / cmin G ≤ gConst n d m ^ m)
    (l : List (Config G)) (c cl : Config G) (hl : PhaseRun G d m sinit l) (hc : l.head? = some c)
    (hcl : l.getLast? = some cl) (u : Fin n) (hu : u ∈ c.F) (ε : ℝ) (hε : 0 < ε) :
    privateCost G cl.s u ≤
        (1 + ε) * privateCost G c.s u +
          (1 + 1 / ε) ^ d * (d : ℝ) ^ d * partialPot G (cfgMovers l) c.s ∧
      ∀ t : G.Strategy u,
        1 / (1 + ε) * privateCost G (Function.update c.s u t) u -
            (1 + 1 / ε) ^ d * (d : ℝ) ^ d / (1 + ε) * partialPot G (cfgMovers l) c.s ≤
          privateCost G (Function.update cl.s u t) u := by sorry

end WeightedCongestionBR
