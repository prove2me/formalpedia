-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidEquations_fcfs_fluid_equation_corrected
-- name    : ProcessingNetworks.FluidEquations.fcfs_fluid_equation_corrected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:34:27.044799+00:00
-- url     : https://prove2.me/theorems/73e65739-1fa3-4bda-ab0e-8a38db774170
-- title:
--   Theorem 7.5 (FCFS fluid equation), with fluid paths on $t \ge 0$ and nonnegative service times
-- statement:
--   This is Theorem 7.5 of Dai and Harrison (the FCFS fluid equation), stated with the two conventions that the book uses implicitly: fluid paths are considered only on $[0,\infty)$, and service times are nonnegative.
--
--   Consider a queueing network with classes $i\in\mathcal I=\{1,\dots,I\}$ and single-server pools $k\in\mathcal K$ ($b_k=1$). Each class $i$ is served by pool $p(i)$, and $I(k)=\{i: p(i)=k\}$ is the set of classes served by pool $k$. The network runs under the first-come-first-served (FCFS) policy, in the sample-path form (7.12):
--   $$
--   D^x_i\big(t+W^x_k(t)\big)=Z^x_i(0)+G^x_i(t),\qquad i\in I(k),
--   $$
--   where $G^x$ counts cumulative external and internal arrivals (7.10) and $W^x_k$ is the immediate workload of pool $k$ (7.11).
--
--   Let $(\hat D,\hat F,\hat T,\hat Z)$ be a fluid limit path. It is witnessed by a sample point $\omega$ and initial states $x_n$ with $|x_n|\to\infty$, and the fluid-scaled processes converge uniformly on compact sets. At $\omega$ the following hold:
--
--   1. the strong laws of large numbers (2.14) and (2.15), with arrival rates $\lambda_i$, mean service times $m_i$ and routing probabilities $P_{ji}$;
--   2. condition (6.38) on the largest service time;
--   3. all service times $v_j(\ell)$ and all residual service times of the initial services are nonnegative.
--
--   Then for all $s,t\ge 0$, all $i$ and all $k$:
--
--   1. $\hat Z_i(t)=\hat Z_i(0)+\lambda_i t+\sum_j P_{ji}\hat F_j(t)-\hat D_i(t)$;
--   2. $\hat Z_i(t)\ge 0$;
--   3. $\hat D_i(t)=\hat F_i(t)$;
--   4. $m_i\hat F_i(t)=\hat T_i(t)$;
--   5. $\hat T(0)=0$, and $\hat T$ is nondecreasing on $[0,\infty)$;
--   6. $\sum_{i\in I(k)}\big(\hat T_i(t)-\hat T_i(s)\big)\le b_k(t-s)$ for $s\le t$;
--
--   and, for $t\ge 0$ and $i\in I(k)$, the FCFS fluid equation holds:
--   $$
--   \hat D_i\Big(t+\sum_{l\in I(k)} m_l\hat Z_l(t)\Big)=\hat Z_i(0)+\lambda_i t+\sum_j P_{ji}\hat D_j(t).
--   $$
--
--   Together these are the fluid equations (6.1)–(6.6) specialized to queueing networks, plus the time-shifted identity (7.13)–(7.15). The identity is the deterministic constraint that FCFS imposes on every fluid limit, and it is the starting point for stability or instability arguments about FCFS networks.
--
--   **Formalization Note.** This statement differs from the mission goal `ProcessingNetworks.FluidEquations.fcfs_fluid_equation` in two places, and both are needed for the goal to be provable. First, monotonicity of $\hat T$ is asserted only on $[0,\infty)$ (`MonotoneOn Th (Set.Ici 0)`): the hypotheses do not constrain `Th` at negative times, so the goal's `Monotone Th` cannot be derived. Second, the hypotheses `hv` and `hPsi` make service times and initial residual times nonnegative at $\omega$. Without them the time $t+\hat W_k(t)$ can be negative, where $\hat D$ is unconstrained. All other hypotheses are copied verbatim from the goal.
-- source:
--   J. G. Dai and J. M. Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, http://spnbook.org — Theorem 7.5, p. 131 (PDF p. 147), Eqs. (7.10)-(7.15); fluid equations (6.1)-(6.6) and Theorem 6.5; SLLNs (2.14), (2.15) and condition (6.38).

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations

namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

theorem fcfs_fluid_equation_corrected
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hfcfs : FCFS dat fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
    (hv : ∀ j ℓ, 0 ≤ v j ℓ ω)
    (hPsi : ∀ (y : Xstate) j k, k < (Mrep.f y).1 j → 0 ≤ (fam.Psi y j k ω).1)
    (h214 : ∀ i, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (dat.lam i)))
    (h215 : ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop
        (nhds (dat.m j)) ∧
      ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop
        (nhds (dat.P j i)))
    (h638 : ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v i ℓ ω) atTop (nhds 0))
    (hDcont : Continuous Dh) (hFcont : Continuous Fh) (hTcont : Continuous Th)
    (hZcont : Continuous Zh) (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hD : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.D (x n) (Mrep.size (x n) * t) ω i : ℝ)) Dh)
    (hF : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω i : ℝ)) Fh)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh) :
    ((∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Fh t j - Dh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Fh t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, dat.m i * Fh t i = Th t i) ∧
      (Th 0 = 0 ∧ MonotoneOn Th (Set.Ici 0)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k,
        ∑ i ∈ poolBuffers dat k, (Th t i - Th s i) ≤ dat.b k * (t - s))) ∧
    ∀ (t : ℝ) (k : Fin K) (i : Fin I), 0 ≤ t → i ∈ poolBuffers dat k →
      Dh (t + ∑ l ∈ poolBuffers dat k, dat.m l * Zh t l) i
        = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Dh t j := by sorry

end ProcessingNetworks.FluidEquations
