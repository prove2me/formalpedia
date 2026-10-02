-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidStability_fluid_limit_stability_implies_spn_stability
-- name    : ProcessingNetworks.FluidStability.fluid_limit_stability_implies_spn_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:39:15.215965+00:00
-- url     : https://prove2.me/theorems/31603a55-7bef-4de0-974b-6628f69beeea
-- title:
--   Theorem 6.2 — fluid limit stability implies SPN stability (goal)
-- statement:
--   This is the goal theorem of the mission — the result the book itself introduces as **"the
--   fulcrum that supports all other results developed in this book."** Every later chapter proves
--   stability of some specific queueing model or control policy by (a) deriving extra,
--   policy-specific fluid equations beyond (6.1)-(6.6), (b) exhibiting a Lyapunov function forcing
--   every fluid model solution's buffer contents to reach zero in finite time (i.e. establishing
--   `FluidModelStable`, hence via Theorem 6.5 also `FluidLimitStable`), and then (c) invoking this
--   theorem to conclude the original stochastic model is stable.
--
--   **Theorem 6.2.** If the fluid limit of an SPN is stable (Definition 6.1), then the SPN is
--   also stable, that is, its ambient Markov chain $X$ is positive recurrent (Definition 3.6).
--
--   **Formalization note.** The proof (not carried out here) combines Theorem 6.5 (every
--   unbounded sequence of initial states has a fluid-limit subsequence, and it is a fluid model
--   solution), Lemma 6.10 (uniform integrability of scaled buffer contents), and mission
--   01's Lemma 3.7 (a drift condition sufficient for positive recurrence) — `FluidLimitStable`
--   supplies exactly the drift bound Lemma 3.7 needs, uniformly over initial states, via Theorem
--   6.5's convergence and Lemma 6.10's uniform integrability (which upgrades the a.s. convergence
--   $\hat Z^{x_n}(h) \to 0$ implicit in fluid limit stability to convergence of expectations,
--   Theorem B.2), and the standard setup's identification $Z^x(t) \sim Z(t) \mid X(0) = x$, which
--   turns $\mathbb{E}[Z^x(|x|\delta)]$ into the $\mathbb{E}_x[Z(|x|\delta)]$ of (3.5). The SPN is
--   Section 6.3's standard setup `fam` under Assumption 2.1(a)–(c) for the core stochastic elements,
--   with `dat` the corresponding fluid-equation data. `IsStable` is mission 01's Definition 3.6
--   predicate (positive recurrence of the ambient continuous-time chain), so this theorem's
--   conclusion is literally what every later mission in the series means by "the SPN is stable."
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 106, Theorem 6.2

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily
import Definitions.Def_ProcessingNetworks_FluidStability_FluidLimitPath
import Definitions.Def_ProcessingNetworks_FluidStability_FluidLimitStable

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability
open scoped NNReal

/-- Theorem 6.2, Dai & Harrison p. 106 (PDF p. 122) — the goal theorem of this mission, "the
fulcrum that supports all other results developed in this book": if the fluid limit of an SPN is
stable (Definition 6.1), then the SPN is also stable, that is, its ambient Markov chain `X` is
positive recurrent (Definition 3.6). The SPN is given through Section 6.3's standard setup `fam`
(one version per initial state, built by the Chapter 2 mechanics from the core stochastic
elements `E, v, φ`, which satisfy Assumption 2.1(a)–(c)), and the fluid-equation data `dat` are
the model data `sd` together with the means `Γ`, `m` and the arrival rates `lam` of that
assumption. -/
theorem fluid_limit_stability_implies_spn_stability
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    {lam : Fin I → ℝ≥0} {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ}
    (ba : CoreStochasticAssumptions I J E lam v φ m Γ)
    (hdat : dat = ⟨sd.B, fun i j => Γ j i, m, sd.A, sd.b, fun i => (lam i : ℝ)⟩)
    (hfl : FluidLimitStable fam) :
    IsStable Mrep := by sorry

end ProcessingNetworks.FluidStability
