-- Prove2me | Theorems.Thm_ProcessingNetworks_TaskAllocation_fluid_limit_existence_and_wwta_equation
-- name    : ProcessingNetworks.TaskAllocation.fluid_limit_existence_and_wwta_equation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:42:14.650136+00:00
-- url     : https://prove2.me/theorems/5f7336a5-be7d-440f-8e74-24603488e661
-- title:
--   Theorem 11.4 — fluid limit existence, the fluid equations, and the WWTA equation (milestone)
-- statement:
--   **Theorem 11.4.** Consider the task allocation model with a simply structured routing policy.
--   (a) For almost all $\omega$ there exist fluid limit paths (Definition 6.6). (b) Each fluid
--   limit path $(\hat D,\hat E,\hat T,\hat W,\hat Z)$ satisfies the fluid model equations
--   (11.11)-(11.15). (c) Under the WWTA routing policy, each fluid limit path further satisfies
--   (11.16).
--
--   **Formalization note.** Following mission III's own `fluid_limit_existence` (Theorem 6.5), a
--   sample point `ω` is fixed together with the SLLN hypotheses the book's proof fixes — (2.14) with
--   $U_\ell$ in place of $E_i$ (Proposition E.7's SLLN for the MArP, `hU`), (2.15) for the service
--   times of every class (`h215`) and the negligibility condition (6.38) (`h638`) — rather than
--   using a measure-theoretic "for almost all `ω`" quantifier; parts (a)–(c) are stated for fluid
--   limit paths along that `ω` (`FluidLimitPathAt`), which is what the book proves. Part (c)'s WWTA
--   hypothesis (`hWWTA`) is stated at the raw (pre-limit) process level, as the direct
--   domination/non-routing consequence the book's own ε-δ argument derives from Definition 11.3's
--   discrete policy (a strictly dominated server receives no category-$\ell$ task for a while),
--   rather than by re-deriving that consequence from `IsWWTA` applied to an explicit arrival sequence
--   — a documented scope simplification (see `MODERATION_NOTES.md`). The model itself is the
--   standard setup `TaskAllocationProcessFamily`, whose relations (11.9)–(11.10), the single-server
--   non-idling service mechanism and (6.51) are what the proofs of (a), (11.12) and (11.15) use.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 217-219, Theorem 11.4, Eqs. (11.11)-(11.22)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_WWTA
import Definitions.Def_ProcessingNetworks_TaskAllocation_FluidModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_AmbientChain
import Definitions.Def_ProcessingNetworks_TaskAllocation_ProcessFamily

namespace ProcessingNetworks.TaskAllocation

open MeasureTheory Filter ProcessingNetworks.Stability

/-- Theorem 11.4, Dai & Harrison p. 217 (PDF p. 233). Consider the task allocation model (the
standard setup `fam`) with a simply structured routing policy. Following mission III's own
`fluid_limit_existence` (Theorem 6.5), the sample point `ω` is fixed as a hypothesis at which the
SLLNs hold — (2.14) with `U_ℓ` in place of `E_i` (Proposition E.7's SLLN for the MArP, `hU`),
(2.15) for the service times of every class (`h215`), and the negligibility condition (6.38)
(`h638`) — rather than "for almost all `ω`". (a) For any unbounded set `C` of initial states
there is a sequence in `C` with `|xₙ| → ∞` along which the fluid-scaled processes converge u.o.c.
to a fluid limit path. (b) Each fluid limit path along `ω` satisfies the fluid model equations
(11.11)–(11.15). (c) Under the WWTA routing policy — `hWWTA`, the pre-limit consequence of
Definition 11.3's argmin rule that the book's proof of (11.22) uses: whenever server `k` is
strictly dominated for category `ℓ` at time `t`, no category-`ℓ` task is routed to `k` for a
while after `t` — each fluid limit path along `ω` further satisfies (11.16). -/
theorem fluid_limit_existence_and_wwta_equation
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {L K : ℕ} [Nonempty (Fin K)]
    (dat : TaskAllocationData L K)
    {N : ℝ → Ω → Fin (L * K) → ℕ} {Z : ℝ → Ω → Fin (L * K) → ℕ}
    {Mrep : MarkovRepresentation Xstate (L * K) (L * K) N Z}
    {U : Fin L → ℝ → Ω → ℕ} {v : Fin L → Fin K → ℕ → Ω → ℝ}
    (fam : TaskAllocationProcessFamily dat Mrep U v) (ω : Ω)
    (hU : ∀ ℓ, Tendsto (fun t : ℝ => (U ℓ t ω : ℝ) / t) atTop (nhds (dat.nu ℓ)))
    (h215 : ∀ ℓ k, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, v ℓ k j ω) / n) atTop
      (nhds (dat.m ℓ k)))
    (h638 : ∀ ℓ k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ j ∈ Finset.range n, v ℓ k j ω) atTop
      (nhds 0))
    (hWWTA : ∀ x (t : ℝ), 0 ≤ t → ∀ (ℓ : Fin L) (k k' : Fin K),
      dat.m ℓ k * workload dat (fun ℓ' k'' => (fam.Zx x t ω ℓ' k'' : ℝ)) k >
          dat.m ℓ k' * workload dat (fun ℓ' k'' => (fam.Zx x t ω ℓ' k'' : ℝ)) k' →
        ∃ δ : ℝ, 0 < δ ∧ fam.E x (t + δ) ω ℓ k = fam.E x t ω ℓ k)
    (C : Set Xstate) (hC : ¬ BddAbove (Mrep.size '' C)) :
    (∃ xseq : ℕ → Xstate, (∀ n, xseq n ∈ C) ∧
      ∃ Eh Dh Zh : ℝ → Fin L → Fin K → ℝ, FluidLimitPathAt fam ω xseq Eh Dh Zh) ∧
    (∀ (xseq : ℕ → Xstate) (Eh Dh Zh : ℝ → Fin L → Fin K → ℝ),
      FluidLimitPathAt fam ω xseq Eh Dh Zh →
        ∃ Wh : ℝ → Fin K → ℝ, IsTaskAllocationFluidModelSolution dat Eh Dh Wh Zh) ∧
    (∀ (xseq : ℕ → Xstate) (Eh Dh Zh : ℝ → Fin L → Fin K → ℝ),
      FluidLimitPathAt fam ω xseq Eh Dh Zh →
        ∀ Wh : ℝ → Fin K → ℝ, IsTaskAllocationFluidModelSolution dat Eh Dh Wh Zh →
          SatisfiesWWTAFluidEquation dat Eh Wh) := by sorry

end ProcessingNetworks.TaskAllocation
