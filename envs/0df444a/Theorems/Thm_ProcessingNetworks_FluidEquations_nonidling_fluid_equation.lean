-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidEquations_nonidling_fluid_equation
-- name    : ProcessingNetworks.FluidEquations.nonidling_fluid_equation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:48:12.374636+00:00
-- url     : https://prove2.me/theorems/1cba1dd8-e57f-435d-bd2f-17f39d16ec4b
-- title:
--   Theorem 7.2 — fluid equation for a non-idling policy (milestone)
-- statement:
--   A control policy for a queueing network is **non-idling** if no server remains idle while a
--   job is waiting in one of the buffers it processes.
--
--   **Theorem 7.2.** For a queueing network operating under a non-idling policy, each fluid limit
--   path $(\hat D, \hat F, \hat T, \hat Z)$ satisfies (7.1): for each pool $k$ and each $t > 0$,
--   $$
--   \sum_{i \in I(k)} \hat Z_i(t) > 0 \quad\Longrightarrow\quad
--   \frac{d}{dt}\Big(\sum_{i \in I(k)} \hat T_i(t)\Big) = b_k.
--   $$
--
--   This is the simplest of the chapter's policy-specific fluid equations, and the template for
--   the rest: derive a conditional identity ("fluid present $\Rightarrow$ full service") from a
--   qualitative property of the control policy.
--
--   **Formalization note.** The conclusion is genuinely conditional (`HasDerivAt`, only under the
--   hypothesis `hz`), not an unconditional identity for all $t$: Remark 7.1 explicitly notes that
--   individual components $\hat T_i$ need not be differentiable at $t$, only the pool-wide sum,
--   and only where fluid is present. `NonIdling` packages the sample-path content of the
--   non-idling policy — full service whenever at least $b_k$ jobs are present, the identity (7.4)
--   — see that item's own notes for the precise correspondence with the book's verbal definition.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 126, Theorem 7.2

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations

namespace ProcessingNetworks.FluidEquations

open MeasureTheory ProcessingNetworks.Stability

/-- Theorem 7.2, Dai & Harrison p. 126 (PDF p. 142): for a queueing network operating under a
non-idling policy (`NonIdling dat fam`, the sample-path identity (7.4)), each fluid limit path
satisfies the fluid equation (7.1): for each pool `k` and each `t > 0`, `∑_{i∈I(k)} Ẑᵢ(t) > 0`
implies `d/dt (∑_{i∈I(k)} T̂ᵢ(t)) = bₖ`. -/
theorem nonidling_fluid_equation
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hni : NonIdling dat fam)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) (dat.b k) t := by sorry

end ProcessingNetworks.FluidEquations
