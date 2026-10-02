-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidStability_scaled_buffer_contents_uniformly_integrable
-- name    : ProcessingNetworks.FluidStability.scaled_buffer_contents_uniformly_integrable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:38:28.850169+00:00
-- url     : https://prove2.me/theorems/7577c55d-390a-404f-9e0c-19e2ed4434e2
-- title:
--   Lemma 6.10 — uniform integrability of scaled buffer contents
-- statement:
--   **Lemma 6.10.** Fix $h > 0$. The family of random variables
--   $$
--   \left\{ \frac{1}{|x|} Z^x(|x|h)\ :\ x \in \mathcal X,\ |x| \ge 1 \right\}
--   $$
--   is uniformly integrable.
--
--   Uniform integrability of the fluid-scaled buffer-content family is the ingredient — alongside
--   Theorem 6.5 and the drift criterion Lemma 3.7 — that lets fluid limit stability be converted
--   into the drift condition (3.5) needed to invoke Lemma 3.7 and conclude positive recurrence,
--   which is exactly the content of the goal theorem's proof.
--
--   **Formalization note.** "Uniformly integrable" (Definition B.1) is Mathlib's
--   `MeasureTheory.UnifIntegrable` at exponent $p = 1$: for every $\varepsilon > 0$ there is a
--   $\delta > 0$ such that every member of the family has $L^1$-norm at most $\varepsilon$ when
--   restricted to any set of measure at most $\delta$ — the standard "uniformly absolutely
--   continuous integrals" meaning of uniform integrability, matching the book's own citation of
--   Definition B.1. The index family is the subtype `{x : Xstate // 1 ≤ spnSize Mrep x}`, matching
--   "$x \in \mathcal X$ with $|x| \ge 1$" exactly. The lemma is stated under the standard setup
--   `SPNProcessFamily` and Assumption 2.1(a)–(c) for the core stochastic elements
--   (`CoreStochasticAssumptions`), which supply the finite means the proof's bounds rest on, with
--   the fluid-equation data `dat` identified with the model data and those means.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 122, Lemma 6.10

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability
open scoped NNReal

/-- Lemma 6.10, Dai & Harrison p. 122 (PDF p. 138): fix `h > 0`. The family of random variables
`{ (1/|x|) Z^x(|x|h), x ∈ 𝒳 with |x| ≥ 1 }` is uniformly integrable (Definition B.1, formalized
by Mathlib's measure-theoretic `UnifIntegrable` at `p = 1`, "uniformly absolutely continuous
integrals," the standard meaning of Definition B.1). The SPN is Section 6.3's standard setup `fam`
under Assumption 2.1(a)–(c) for the core stochastic elements, with `dat` the corresponding
fluid-equation data. -/
theorem scaled_buffer_contents_uniformly_integrable
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    {lam : Fin I → ℝ≥0} {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ}
    (ba : CoreStochasticAssumptions I J E lam v φ m Γ)
    (hdat : dat = ⟨sd.B, fun i j => Γ j i, m, sd.A, sd.b, fun i => (lam i : ℝ)⟩)
    (h : ℝ) (hh : 0 < h) :
    UnifIntegrable
      (fun x : {x : Xstate // 1 ≤ spnSize Mrep x} => fun ω : Ω =>
        (spnSize Mrep (x : Xstate))⁻¹ •
          fun i => (fam.Zx (x : Xstate) (spnSize Mrep (x : Xstate) * h) ω i : ℝ))
      1 (ℙ : Measure Ω) := by sorry

end ProcessingNetworks.FluidStability
