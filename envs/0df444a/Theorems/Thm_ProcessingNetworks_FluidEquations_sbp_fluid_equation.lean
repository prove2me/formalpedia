-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidEquations_sbp_fluid_equation
-- name    : ProcessingNetworks.FluidEquations.sbp_fluid_equation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:48:43.437525+00:00
-- url     : https://prove2.me/theorems/3a26d45b-2d9c-4006-bcfb-71c1d0c05917
-- title:
--   Theorem 7.3 — fluid equation for a non-preemptive SBP policy (milestone)
-- statement:
--   An SBP policy is **non-preemptive** if a job in service is never interrupted, even by the
--   later arrival of a higher-priority job at the same pool.
--
--   **Theorem 7.3.** For a queueing network operating under a non-preemptive SBP policy with
--   priority permutation $\sigma$, each fluid limit path $(\hat D, \hat F, \hat T, \hat Z)$
--   satisfies (7.6): for each buffer $j$ and each $t > 0$,
--   $$
--   \sum_{i \in H(j)} \hat Z_i(t) > 0 \quad\Longrightarrow\quad
--   \frac{d}{dt}\Big(\sum_{i \in H(j)} \hat T_i(t)\Big) = b_{p(j)},
--   $$
--   where $H(j)$ (Eq. 7.5) is the set of same-pool buffers with priority at least as high as
--   $j$'s and $p(j)$ is the pool serving class $j$.
--
--   This generalizes Theorem 7.2 (which is the special case $H(j) = I(p(j))$, i.e. no priority
--   distinctions within a pool) and generalizes Eq. (6.15)'s criss-cross-network fluid equation,
--   stated there without proof.
--
--   **Formalization note.** The hypothesis `hsbp` is the two-sided bound (7.7) that the
--   non-preemptive policy gives (see `PolicyRelations`); the exact identity (7.4) with $H(j)$ holds
--   only under preemption (Remark 7.4). Because the proof's steps (7.8)–(7.9) use the condition
--   (6.38) at the sample point $\omega$ of the fluid limit path, and the stochastic bound (6.36)
--   of the standard setup, the fluid limit path is given here by its witnessing $(\omega, \{x_n\})$
--   together with the u.o.c. convergences (6.39) along it, exactly as the book's proof fixes them;
--   the theorem's own conclusion, the conditional derivative identity for $H(j)$, is otherwise
--   stated exactly as `nonidling_fluid_equation`'s, with $I(k)$ replaced by $H(j)$ and $b_k$ by
--   $b_{p(j)}$ throughout, matching the book's own remark that "the proof mimics that of Theorem
--   7.2."
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 128, Theorem 7.3

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_Hset
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations

namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

/-- Theorem 7.3, Dai & Harrison p. 128 (PDF p. 144): for a queueing network operating under a
non-preemptive static-buffer-priority (SBP) policy with priority ranking `σ`
(`SBPNonPreemptive dat σ fam`, the two-sided bound (7.7)), each fluid limit path satisfies the
fluid equation (7.6): for each buffer `j` and each `t > 0`, `∑_{i∈H(j)} Ẑᵢ(t) > 0` implies
`d/dt (∑_{i∈H(j)} T̂ᵢ(t)) = b_{p(j)}`. The fluid limit path is given by its witnessing sample
point `ω` and initial-state sequence `x` (the proof's (7.8)–(7.9) use the condition (6.38) at
that `ω`, `(1/n) max_{ℓ ≤ n} v_i(ℓ) → 0`, to show the remaining-processing-time term of (7.7)
is negligible), together with the u.o.c. convergences (6.39) along `(ω, x)`. -/
theorem sbp_fluid_equation
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ)
    (σ : Equiv.Perm (Fin I)) (hsbp : SBPNonPreemptive dat σ fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
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
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh)
    (j : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ Hset dat σ j, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ Hset dat σ j, Th s i) (dat.b (dat.p j)) t := by sorry

end ProcessingNetworks.FluidEquations
