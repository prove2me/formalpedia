-- Prove2me | Theorems.Thm_WeightedCongestionBR_theorem_3
-- name    : WeightedCongestionBR.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:35.466479+00:00
-- url     : https://prove2.me/theorems/75674f3a-b87a-404e-b41c-1e7acdc8843f
-- title:
--   Theorem 3 (Key Property) — $\Phi_{R_i}(s^{i-1})\le n p b_i$, for every prefix of phase $i$
-- statement:
--   Throughout, $\Gamma$ is a weighted polynomial congestion game of degree $d\ge1$ with weights $w_u\ge1$, $s_{\mathrm{init}}$ is an initial state with $c_{\min}>0$, and $m\ge1$ is an integer with $c_{\max}/c_{\min}\le g^m$ (Algorithm 1's parameters). For every phase $i\ge1$ of Algorithm 1,
--
--   $$
--   \Phi_{R_i}(s^{i-1})\le n\,p\,b_i .
--   $$
--
--   Stated for every prefix of phase $i$: if phase $i\ge1$ begins at state $s^{i-1}$ and $R$ is the set of players that have moved in phase $i$ so far, then $\Phi_R(s^{i-1})\le npb_i$. For the complete phase, $R=R_i$.
--
--   It bounds the number of moves of each phase (Theorem 4) and the cost drift of fixed players (Theorem 5).
--
--   Differences from the source:
--   - generalization: R_i, the players that move during the whole phase i → the players that move in any prefix of phase i (the phase need not have ended); reason: the proof uses only the moves made, and the complete phase is a prefix; this form is what the termination argument of Theorem 4 needs before it knows that phase i ends
--   - generalization: m = log(c_max/c_min) (Line 1) → any integer m ≥ 1 with c_max/c_min ≤ g^m, g computed from m; reason: Reading 2: Line 1's m must be an integer; ⌈log(c_max/c_min)⌉ clamped to 1 is one such m, and the proof uses only m ≥ 1 and b_m ≤ c_min
--   - encoding: c_min used as a divisor in Line 1 → hypothesis 0 < c_min; reason: Reading 3: with c_min = 0 the value m = log(c_max/0) is undefined; the hypothesis excludes only those undefined cases
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 3, p.16 (proof pp.17–18 and Appendix B, pp.26–27)

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
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Theorem 3 (Key Property)** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.16; proof pp.17–18 and Appendix B). For every phase `i ≥ 1`
of the algorithm, `Φ_{R_i}(s^{i−1}) ≤ n p b_i`.

Stated for every prefix of phase `i`: if `l` starts at the configuration where phase `i ≥ 1` begins
(its state is `s^{i−1}`) and continues with best-response moves of phase `i`, and `R` is the set of
players that moved along `l`, then `Φ_R(s^{i−1}) ≤ n p b_i`. For the whole phase, `R = R_i`.

**Formalization Note** Hypotheses of Algorithm 1: the game is polynomial of degree `d ≥ 1`, weights
satisfy `w_u ≥ 1` (p.6), `1 ≤ m`, `0 < c_min` and `c_max/c_min ≤ g^m` (Line 1 with `m` any integer
satisfying them, Readings 2 and 3). -/
theorem theorem_3 {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u) (hm : 1 ≤ m)
    (hcmin : 0 < cmin G) (hratio : cmax G sinit / cmin G ≤ gConst n d m ^ m)
    (l : List (Config G)) (c : Config G) (hl : PhasePrefix G d m sinit l) (hc : l.head? = some c)
    (hi : 1 ≤ c.phase) :
    partialPot G (cfgMovers l) c.s ≤ n * pConst d * bnd G d m sinit c.phase := by sorry

end WeightedCongestionBR
