-- Prove2me | Theorems.Thm_WeightedCongestionBR_algorithm1_polytime_approx_equilibrium
-- name    : WeightedCongestionBR.algorithm1_polytime_approx_equilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:58.036575+00:00
-- url     : https://prove2.me/theorems/169c280f-9f50-4d9a-91d1-48a7e9885d9c
-- title:
--   Theorems 4 and 6 — Algorithm 1 runs in polynomial time and ends in a $d^{d+o(d)}$-approximate equilibrium
-- statement:
--   **Theorem 4.** Algorithm 1 runs in time polynomial in the number of bits of the representation of its input game $\Gamma$. **Theorem 6.** At the end of Algorithm 1, all players are in a $d^{d+o(d)}$-equilibrium.
--
--   Let $d\ge1$, $\alpha=d+1$, $p=(2d+3)(d+1)(4d)^{d+1}$ and $\bar\rho(d)=p(1+3p^{-1})/(1-2p^{-1})$. For every weighted polynomial congestion game $\Gamma$ of degree $d$ (weights $w_u>0$), every initial state $s_{\mathrm{init}}$ with $c_{\min}>0$ and every integer $m\ge1$ with $c_{\max}/c_{\min}\le g^m$:
--
--   1. **Termination.** Every run of Algorithm 1 makes at most $T(n,m,d)=n\alpha g(\alpha p+1)+(m-1)ng(\alpha p+1)p$ best-response moves and at most $T(n,m,d)+m$ steps; every reachable configuration before the end has a successor; and the end (phase $m$) is reachable.
--   2. **Guarantee.** Every reachable final state $s$ is a $\bar\rho(d)$-equilibrium: $C_u(s)\le\bar\rho(d)\,C_u(s_{-u},s'_u)$ for all players $u$ and all $s'_u\in S_u$.
--
--   Moreover:
--
--   3. **The factor.** $\bar\rho(d)=d^{d+o(d)}$, that is
--
--   $$
--   \log_d\bar\rho(d)-d=o(d)\qquad(d\to\infty).
--   $$
--
--   4. **Time.** For every $d\ge1$ and every polynomial $B$ bounding the time of a best-response call there is a polynomial $P$, depending only on $d$ and $B$, such that on every rational instance $\Gamma$ of degree $d$, for every $s_{\mathrm{init}}$ with $c_{\min}>0$, every $m$ with $1\le m\le1+\lceil\log_2(c_{\max}/c_{\min})\rceil$ and $c_{\max}/c_{\min}\le g^m$, every best-response cost $t_{BR}\le B(\sigma(\Gamma))$ and every run, the running time is at most $P(\sigma(\Gamma))$.
--
--   The previous best deterministic factor for this problem was $d^{2d+o(d)}$; this algorithm runs best-response dynamics in the original game.
--
--   Differences from the source:
--   - reading: 'runs in time polynomial in the number of bits' with d constant and best responses assumed polynomial-time (footnote 15), no machine named → runTime: (n+m+3)L² + n t_BR + (k+1) n (t_BR + (2|E|(n+d+2)+3)L²) with L the largest bit length of the numbers handled, bounded by P(σ(Γ)) with P chosen from d and the oracle bound B; reason: Reading 1: an accounting at the level of the pseudocode with a best-response oracle, as the paper's proof counts phases and moves; a machine executing the pseudocode obeys it
--   - generalization: m = log(c_max/c_min) (Line 1) → any integer m ≥ 1 with c_max/c_min ≤ g^m, g computed from m; reason: Reading 2: Line 1's m must be an integer; ⌈log(c_max/c_min)⌉ clamped to 1 is one such m, and the proof uses only m ≥ 1 and b_m ≤ c_min
--   - encoding: c_min used as a divisor in Line 1 → hypothesis 0 < c_min; reason: Reading 3: with c_min = 0 the value m = log(c_max/0) is undefined; the hypothesis excludes only those undefined cases
--   - reading: d^{d+o(d)}-equilibrium (Theorem 6) → ρ̄(d) = p(1+3p⁻¹)/(1−2p⁻¹)-equilibrium, with log_d ρ̄(d) − d = o(d) as d → ∞; reason: Reading 5: the proof of Theorem 6 obtains exactly the factor ρ̄(d); d^{d+o(d)} is an asymptotic statement about it
--   - reading: '∃u' in Lines 6 and 9 and an arbitrary tie-break of BR_u → nondeterministic step relation; every selection of player and best response; reason: Reading 6: the paper's claims hold for every selection, so all are covered
--   - generalization: Theorem 4: polynomial running time → adds the explicit bound T(n,m,d) on the moves of every run, reachability of the end, and the existence of a successor before the end; reason: these are the counts the proof of Theorem 4 establishes (p.19); they also make the guarantee non-vacuous
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
--   - generalization: the number of bits of the representation of the input game Γ (which includes the strategy sets and s_init) → σ(Γ) = n + |E| + Σ_u ℓ(w_u) + Σ_{e,ν≤d} ℓ(a_{e,ν}), strategy sets and s_init not counted; oracle time t_BR ≤ B(σ(Γ)); reason: σ(Γ) is at most the full input length, so a bound P(σ(Γ)) implies a polynomial bound in the full input length; footnote 15 assumes best responses computable in polynomial time
--   - reading: m = log(c_max/c_min) in the running-time claim → in (D), m is any integer with 1 ≤ m ≤ 1 + ⌈log₂(c_max/c_min)⌉ and c_max/c_min ≤ g^m; reason: Reading 2: Line 1's m rounded up (and clamped to 1) satisfies both bounds for a logarithm of base 2 or e; an unbounded m would make the running time unbounded, which the paper excludes by fixing m
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 4, p.18, and Theorem 6, p.21

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
import Definitions.Def_WeightedCongestionBR_IsGroupEq
import Definitions.Def_WeightedCongestionBR_rhoBar
import Definitions.Def_WeightedCongestionBR_moveBound
import Definitions.Def_WeightedCongestionBR_IsRun
import Definitions.Def_WeightedCongestionBR_numMoves
import Definitions.Def_WeightedCongestionBR_RatData
import Definitions.Def_WeightedCongestionBR_IsRatInstance
import Definitions.Def_WeightedCongestionBR_sigmaSize
import Definitions.Def_WeightedCongestionBR_runTime
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Theorem 4 and Theorem 6** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Theorem 4, p.18, and Theorem 6, p.21): Algorithm 1 runs in time
polynomial in the number of bits of the representation of its input game `Γ`, and at the end of
Algorithm 1 all players are in a `d^{d+o(d)}`-equilibrium.

For every weighted polynomial congestion game of degree `d ≥ 1` (weights `w_u > 0`), every initial
state `s_init` with `c_min > 0` and every integer `m ≥ 1` with `c_max/c_min ≤ g^m`:

* (A) every run of Algorithm 1 has at most `T(n, m, d)` best-response moves and at most
  `T(n, m, d) + m` steps, every reachable configuration of a phase `< m` has a successor, and a
  configuration of phase `m` (the end of the algorithm) is reachable;
* (B) the state of every reachable configuration of phase `m` is a `ρ̄(d)`-equilibrium of the game,
  `ρ̄(d) = p(1 + 3p⁻¹)/(1 − 2p⁻¹)`;

and moreover

* (C) `ρ̄(d) = d^{d+o(d)}`: `log_d ρ̄(d) − d = o(d)` as `d → ∞`;
* (D) for every `d ≥ 1` and every polynomial bound `B` on the time of a best-response call there is a
  polynomial `P`, depending only on `d` and `B`, such that on every rational instance of degree `d`,
  for every `s_init` with `c_min > 0`, every `m` with `1 ≤ m ≤ 1 + ⌈log₂(c_max/c_min)⌉` and
  `c_max/c_min ≤ g^m`, and every run, the running time is at most `P(σ(Γ))`.

**Formalization Note** Algorithm 1 is the nondeterministic step relation `AlgStep` (all selections
of players and best responses). `m` is any integer with `1 ≤ m` and `c_max/c_min ≤ g^m` (Reading 2;
Line 1's `log(c_max/c_min)`, rounded up, is one). `c_min > 0` is assumed (Reading 3). The running
time is the cost model `runTime` (Reading 1). -/
theorem algorithm1_polytime_approx_equilibrium :
    (∀ d : ℕ, 1 ≤ d → ∀ {n r : ℕ} (G : Game n r), CongestionApproxPNE.IsPolyGame d G →
      ∀ (sinit : G.Profile) (m : ℕ), 1 ≤ m → 0 < cmin G →
        cmax G sinit / cmin G ≤ gConst n d m ^ m →
        ((∀ l : List (Config G), IsRun G d m sinit l →
            (numMoves l : ℝ) ≤ moveBound n m d ∧ (l.length : ℝ) ≤ moveBound n m d + m + 1) ∧
          (∀ c : Config G, Reach G d m sinit c → c.phase < m →
            ∃ c' : Config G, AlgStep G d m sinit c c') ∧
          (∃ c : Config G, Reach G d m sinit c ∧ c.phase = m)) ∧
        (∀ c : Config G, Reach G d m sinit c → c.phase = m →
          IsGroupEq G (rhoBar d) Finset.univ c.s)) ∧
    (fun d : ℕ => Real.logb (d : ℝ) (rhoBar d) - (d : ℝ)) =o[Filter.atTop] (fun d : ℕ => (d : ℝ)) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ B : Polynomial ℕ, ∃ P : Polynomial ℕ,
      ∀ {n r : ℕ} (G : Game n r) (D : RatData n r d), IsRatInstance G D →
        ∀ sinit : G.Profile, 0 < cmin G → ∀ m : ℕ, 1 ≤ m →
          m ≤ 1 + ⌈Real.logb 2 (cmax G sinit / cmin G)⌉₊ →
          cmax G sinit / cmin G ≤ gConst n d m ^ m →
          ∀ tBR : ℕ, tBR ≤ B.eval (sigmaSize D) →
            ∀ l : List (Config G), IsRun G d m sinit l →
              runTime G D m sinit tBR l ≤ P.eval (sigmaSize D)) := by sorry

end WeightedCongestionBR
