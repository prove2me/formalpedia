-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidEquations_fcfs_fluid_equation
-- name    : ProcessingNetworks.FluidEquations.fcfs_fluid_equation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:49:09.16051+00:00
-- url     : https://prove2.me/theorems/be96c0c0-6b3a-4738-8fd3-5399b0e6a65c
-- title:
--   Theorem 7.5 — fluid equation for FCFS control (goal)
-- statement:
--   Under the FCFS (first-come-first-served) control policy, jobs at a pool are served strictly
--   in arrival order. Let $G_i(t) := E_i(t) + \sum_j \Phi^j_i(D_j(t))$ be the cumulative arrivals
--   (external plus internal) into class $i$, and let $W_k(t)$ be the **immediate workload** at
--   pool $k$: the time needed to clear all jobs at classes $i \in I(k)$ waiting or in service at
--   $t$, assuming no further arrivals. Because FCFS serves in arrival order, all jobs present at
--   a pool at time $t$ finish exactly at $t + W_k(t)$, giving the key identity (7.12):
--   $D_i(t+W_k(t)) = Z_i(0) + G_i(t)$ for $i \in I(k)$.
--
--   **Theorem 7.5 (goal).** For a queueing network under FCFS control, each fluid limit path
--   $(\hat D, \hat F, \hat T, \hat Z)$ satisfies the fluid equations (6.1)-(6.6) and
--   $$
--   \hat D_i\big(t + \hat W_k(t)\big) = \hat G_i(t), \qquad t \ge 0,\ i \in I(k),\ k \in K,
--   $$
--   where $\hat G_i(t) = \lambda_i t + \sum_j P_{ji} \hat D_j(t)$ and
--   $\hat W_k(t) = \sum_{i \in I(k)} m_i \hat Z_i(t)$.
--
--   This is the book's hardest of the three queueing-network policy derivations: unlike the
--   non-idling and SBP fluid equations, which are purely about *when* a pool is busy, the FCFS
--   fluid equation is a genuinely time-shifted identity connecting departures at time
--   $t + \hat W_k(t)$ to arrivals at time $t$, requiring the auxiliary workload process $\hat W$.
--
--   **Formalization note.** $\hat G_i(t) = \lambda_i t + \sum_j P_{ji}\hat D_j(t)$ (7.14) and
--   $\hat W_k(t) = \sum_{i\in I(k)} m_i \hat Z_i(t)$ (7.15) are substituted directly into the
--   conclusion rather than named as separate definitions, since both are fully determined,
--   closed-form expressions in $\hat D$, $\hat Z$ and the model data. The FCFS policy enters through
--   `FCFS dat fam`: single-server pools ($b_k = 1$, the setting the book restricts to) and the raw
--   identity (7.12) with $G$ and $W$ defined by (7.10) and (7.11) from the standard setup's
--   processes and delayed random walk. The fluid limit path is given by its witnessing
--   $(\omega, \{x_n\})$, at which the SLLNs (2.14), (2.15) (with $\Gamma_{ij} = P_{ji}$) and the
--   condition (6.38) hold, together with the u.o.c. convergences (6.39): these are what the book's
--   proof fixes, and what the fluid-equations clause (6.1)–(6.6) of the conclusion (Theorem 6.5's
--   content) requires. The conclusion reads $\hat D_i(t + \hat W_k(t)) = \hat Z_i(0) + \hat G_i(t)$:
--   the term $\hat Z_i(0)$ is the scaled limit of the $Z_i(0)$ in (7.12), and although the book's
--   display (7.13) omits it, its own derivation of (7.13) from (7.12) — and the normalization
--   $|\hat Z(0)| = 1$ of every fluid limit path (Theorem 6.5) — show that it is present; the display
--   as printed would be false for every fluid limit path.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 131, Theorem 7.5

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations

namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

/-- Theorem 7.5, Dai & Harrison p. 131 (PDF p. 147) — the goal theorem of this mission: for a
queueing network with single-server pools operating under the FCFS control policy (`FCFS dat
fam`, the key identity (7.12)), each fluid limit path `(D̂, F̂, T̂, Ẑ)` — given by its witnessing
sample point `ω` and initial-state sequence `x`, at which the SLLNs (2.14), (2.15) and the
condition (6.38) hold, with the u.o.c. convergences (6.39) along `(ω, x)` — satisfies the fluid
equations (6.1)–(6.6) and `D̂ᵢ(t + Ŵₖ(t)) = Ẑᵢ(0) + Ĝᵢ(t)` for each `t ≥ 0`, `i ∈ I(k)`,
`k ∈ K` (7.13), where `Ĝᵢ(t) = λᵢt + ∑ⱼ Pⱼᵢ D̂ⱼ(t)` (7.14) and `Ŵₖ(t) = ∑_{i∈I(k)} mᵢẐᵢ(t)`
(7.15). The term `Ẑᵢ(0)` is the fluid-scaled limit of the `Zᵢ(0)` of (7.12); the book's display
(7.13) omits it, but its own derivation from (7.12) (and the normalization `|Ẑ(0)| = 1` of
Theorem 6.5) show it is present. -/
theorem fcfs_fluid_equation
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hfcfs : FCFS dat fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
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
    IsFluidModelSolutionQN dat Dh Fh Th Zh ∧
    ∀ (t : ℝ) (k : Fin K) (i : Fin I), 0 ≤ t → i ∈ poolBuffers dat k →
      Dh (t + ∑ l ∈ poolBuffers dat k, dat.m l * Zh t l) i
        = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Dh t j := by sorry

end ProcessingNetworks.FluidEquations
