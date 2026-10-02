-- Prove2me | Theorems.Thm_ProcessingNetworks_Subcriticality_processor_sharing_stable_iff_ehl_stable
-- name    : ProcessingNetworks.Subcriticality.processor_sharing_stable_iff_ehl_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:27:23.734272+00:00
-- url     : https://prove2.me/theorems/2d4a9e1c-ef56-4458-9663-b95df82685cb
-- title:
--   Proposition 4.4 — a PS network is stable iff its EHL model is stable
-- statement:
--   Section 4.4 associates to every processor sharing (PS) network an **equivalent head-of-line
--   (EHL) model**: an ordinary relaxed SPN (Section 2.4) obtained by refining each buffer $i$ into
--   classes $(i, s_i)$ indexed by phase-type service phase, and directing all of a refined class's
--   service effort to its single oldest member rather than sharing it. The book shows (Section 4.4)
--   that this construction preserves every transition intensity: the PS model's refined-job-count
--   chain $\eta$ and the EHL model's ambient chain $\tilde\eta$ have literally the same generator
--   matrix, and hence the same recurrence classification.
--
--   **Proposition 4.4.** A PS network is stable (Definition 4.2: $\eta$ positive recurrent) if and
--   only if its EHL model is stable (Definition 3.6).
--
--   **Formalization note.** Rather than re-deriving the EHL construction (the refined-class
--   indexing, the derived phase-type/routing data of Eqs. (4.25)-(4.29)) from a PS network's raw
--   data, the shared-generator fact the book's own proof relies on is taken as an explicit
--   hypothesis, `h_same_generator`: the EHL model's ambient chain — its jump matrix `M.jump` and
--   exit rates `M.rate`, which together are its generator — literally coincides with the PS model's
--   own chain `(jump, rate)`. Given that identification, the equivalence of positive recurrence is
--   immediate, matching the book's own one-line justification ("immediate from the fact that ...
--   have the same generator"). Note that this makes the statement a rendering of the proof's premise
--   rather than of the construction itself.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 79, Proposition 4.4

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Subcriticality_PSNetworkStability

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProcessingNetworks.Stability

/-- Proposition 4.4, p. 79 (PDF p. 95): a processor sharing (PS) network is stable in the sense of
Definition 4.2 if and only if its equivalent head-of-line (EHL) model is stable in the sense of
Definition 3.6. The book's justification (p. 79) is that the refined job-count chain `η` of the PS
model and the ambient chain `η̃` of its EHL model share the same generator matrix by construction
(Section 4.4), and hence the same recurrence classification; `h_same_generator` records that
shared premise: the EHL model's ambient chain (its jump matrix `M.jump` and exit rates `M.rate`,
which together are its generator) coincides with the PS model's own chain `(jump, rate)`. -/
theorem processor_sharing_stable_iff_ehl_stable
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (jump : Xstate → PMF Xstate) (rate : Xstate → ℝ) (M : MarkovRepresentation Xstate I J N Z)
    (h_same_generator : M.jump = jump ∧ M.rate = rate) :
    IsPSStable jump rate ↔ IsStable M := by sorry

end ProcessingNetworks.Subcriticality
