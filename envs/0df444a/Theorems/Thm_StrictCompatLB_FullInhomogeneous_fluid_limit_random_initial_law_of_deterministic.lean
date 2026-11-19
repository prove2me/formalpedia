-- Prove2me | Theorems.Thm_StrictCompatLB_FullInhomogeneous_fluid_limit_random_initial_law_of_deterministic
-- name    : StrictCompatLB.FullInhomogeneous.fluid_limit_random_initial_law_of_deterministic
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:15:33.553932+00:00
-- url     : https://prove2.me/theorems/d517e4da-15f1-451d-8146-909c50ae6ae1
-- title:
--   A fluid limit from deterministic initial states extends to random initial laws concentrating at $q_0$
-- statement:
--   Fix kernels $K_N$ on $\mathbb{N}^N$, rates $r_N$, $N_0$, a limit occupancy $q_0$, a path $s$, $T$ and $\varepsilon$. Suppose that for every sequence of deterministic initial states $z_N$ with $\|\mathrm{occ}(z_N)-q_0\|_1\to 0$ and every choice of uniformized laws $P_N$ (kernel $K_N$, rate $r_N$, initial law the point mass at $z_N$, $N\ge N_0$), $P_N(\sup_{t\le T}\|\mathrm{occ}(X_N(t))-s(t)\|_1\ge\varepsilon)\to 0$. Then the same holds for uniformized laws $P_N$ with arbitrary initial probability vectors $\mu_N$ such that $\mu_N(\|\mathrm{occ}(z)-q_0\|_1\ge\varepsilon')\to 0$ for every $\varepsilon'>0$.
--
--   Proof idea: conditioning a uniformized law on its initial state $z$ (with $\mu_N(z)>0$) gives a uniformized law started at $z$ (the clock is independent of the path); a countable union bound gives $P_N(B)\le\mu_N(F)+\sup_{z\notin F}P_N(B\mid X_0=z)$; a diagonal choice of near-worst initial states with $\mathrm{occ}\to q_0$ (Nat.findGreatest over levels $1/(k+1)$) contradicts the deterministic hypothesis if the conclusion failed.
--
--   Role: reduces the random-initial-law fluid-limit conjunct of Theorem 3.6 to the deterministic-initial-state fluid limit (Theorem 3.4 as stated with $\mathrm{occ}(z_N)\to q_0$).
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Theorem 3.4 p. 12 (initial occupancy converging in probability) and Theorem 3.6 p. 14; conditioning on the initial state: J. R. Norris, Markov Chains (Cambridge 1997), Theorem 1.1.1 and Section 2.6

import Mathlib
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw
import Definitions.Def_StrictCompatLB_FullInhomogeneous_Trajectory

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField StrictCompatLB.Inhomogeneous
open scoped ENNReal NNReal

namespace StrictCompatLB.FullInhomogeneous

theorem fluid_limit_random_initial_law_of_deterministic
    (K : (N : ℕ) → (Fin N → ℕ) → (Fin N → ℕ) → ℝ) (rate : ℕ → ℝ) (N₀ : ℕ)
    (q₀ : ℕ → ℝ) (s : ℝ≥0 → ℕ → ℝ) (T ε : ℝ)
    (hdet : ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
      (∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (fun z => if z = z₀ N then 1 else 0)) →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1
            (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) atTop (𝓝 0))
    (μ : (N : ℕ) → (Fin N → ℕ) → ℝ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ)))
    (hP : ∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (μ N))
    (hμ : ∀ ε' : ℝ, 0 < ε' → Tendsto (fun N => probOf (μ N)
      {z | ENNReal.ofReal ε' ≤ PowerOfDUniversality.Fluid.l1dist (occ z) q₀}) atTop (𝓝 0)) :
    Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1
          (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) atTop (𝓝 0) := by sorry

end StrictCompatLB.FullInhomogeneous
