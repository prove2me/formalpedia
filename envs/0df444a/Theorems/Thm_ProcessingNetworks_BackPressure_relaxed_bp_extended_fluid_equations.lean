-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_relaxed_bp_extended_fluid_equations
-- name    : ProcessingNetworks.BackPressure.relaxed_bp_extended_fluid_equations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:54:59.376022+00:00
-- url     : https://prove2.me/theorems/b9070dd2-a5fb-432e-96b1-1051f5c6b17b
-- title:
--   Lemma 9.11 — the extended relaxed-BP fluid equations (milestone)
-- statement:
--   Augmenting the process with $Y_\beta(t)$, the cumulative time allocation $\beta$ has been
--   employed up to $t$, gives raw identities $T_j = \sum_\beta \beta_j Y_\beta$, $Y_\beta$
--   nondecreasing, $\sum_\beta Y_\beta(t) = t$, and — the substantive content of the policy — a
--   strictly dominated allocation is never employed.
--
--   **Lemma 9.11.** Each fluid limit path $(\hat D,\hat F,\hat T,\hat Z,\hat Y)$ under relaxed BP
--   control satisfies (6.1)-(6.6) plus: $\hat T_j(t) = \sum_{\beta\in E}\beta_j \hat Y_\beta(t)$
--   (9.28); $\hat Y_\beta$ nondecreasing (9.29); $\sum_\beta \hat Y_\beta(t) = t$ (9.30); and
--   $p(\beta,\hat Z(t)) < \max_{\alpha\in E} p(\alpha,\hat Z(t))$ implies $\dot{\hat Y}_\beta(t)=0$
--   (9.31).
--
--   **Formalization note.** The raw hypothesis `hYopt` — a dominated allocation accrues no
--   processing time throughout any interval over which the domination persists — is the natural,
--   non-circular, pre-limit meaning of "the manager always follows the back-pressure rule"; (9.31)
--   is then this fact's genuine fluid-scale consequence (obtained via the $\varepsilon,\delta$
--   continuity argument the book's own proof carries out), not restated as a hypothesis. `hTY`,
--   `hYmono`, `hYsum` are raw identities that hold by the very construction of $Y$ (not
--   policy-specific), included as hypotheses on the raw family for completeness and to make their
--   fluid-scale counterparts' provenance explicit. $E$ is the set of extreme allocations (`hE`),
--   the set from which the policy's solutions are always drawn (Remark 9.7). The lemma's
--   "(6.1)-(6.6)" clause is Theorem 6.5's content and is not restated in the conclusion.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 175, Lemma 9.11

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

namespace ProcessingNetworks.BackPressure

open MeasureTheory

open Filter

/-- Lemma 9.11, Dai & Harrison p. 175 (PDF p. 191): given that Assumption 9.1 holds, each fluid
limit path `(D̂,F̂,T̂,Ẑ,Ŷ)` under the relaxed back-pressure control policy satisfies the basic
fluid equations (6.1)-(6.6) plus (9.28)-(9.31). The raw ("pre-limit") meaning of "operating under
relaxed back-pressure control" is formalized via `hYopt`: a strictly dominated allocation accrues
no additional processing time throughout any raw time interval over which it stays strictly
dominated — the operational content of always selecting an optimal allocation, from which
(9.31)'s fluid-scale statement is obtained by a genuine limit-passage argument (not reproduced
here; see `MODERATION_NOTES.md`). -/
theorem relaxed_bp_extended_fluid_equations
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = ExtremeAllocations dat)
    (Zraw Traw : Xstate → ℝ → Ω → Fin I → ℝ) (Yraw : (Fin J → ℝ) → Xstate → ℝ → Ω → ℝ)
    (Traw' : Xstate → ℝ → Ω → Fin J → ℝ)
    (size : Xstate → ℝ) (size_nonneg : ∀ x, 0 ≤ size x)
    (hTY : ∀ x ω t j, Traw' x t ω j = ∑ β ∈ E, β j * Yraw β x t ω)
    (hYmono : ∀ β ∈ E, ∀ x ω, Monotone (Yraw β x · ω))
    (hYsum : ∀ x ω t, 0 ≤ t → ∑ β ∈ E, Yraw β x t ω = t)
    (hYopt : ∀ β ∈ E, ∀ (x : Xstate) (ω : Ω) (u1 u2 : ℝ), 0 ≤ u1 → u1 ≤ u2 →
      (∀ u ∈ Set.Icc u1 u2, p dat β (Zraw x u ω) < ⨆ α ∈ E, p dat α (Zraw x u ω)) →
      Yraw β x u2 ω = Yraw β x u1 ω)
    (ω : Ω) (x : ℕ → Xstate) (hsize : Tendsto (fun n => size (x n)) atTop atTop)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) (Yh : (Fin J → ℝ) → ℝ → ℝ)
    (hZconv :
      UOCConverges (fun n t i => (size (x n))⁻¹ * Zraw (x n) (size (x n) * t) ω i) Zh)
    (hTconv :
      UOCConverges (fun n t j => (size (x n))⁻¹ * Traw' (x n) (size (x n) * t) ω j) Th)
    (hYconv : ∀ β ∈ E,
      UOCConvergesR (fun n t => (size (x n))⁻¹ * Yraw β (x n) (size (x n) * t) ω) (Yh β)) :
    (∀ t : ℝ, 0 ≤ t → ∀ j, Th t j = ∑ β ∈ E, β j * Yh β t) ∧
    (∀ β ∈ E, Monotone (Yh β)) ∧
    (∀ t : ℝ, 0 ≤ t → ∑ β ∈ E, Yh β t = t) ∧
    (∀ β ∈ E, ∀ t : ℝ, 0 < t → p dat β (Zh t) < ⨆ α ∈ E, p dat α (Zh t) →
      ∀ d : ℝ, HasDerivAt (Yh β) d t → d = 0) := by sorry

end ProcessingNetworks.BackPressure
