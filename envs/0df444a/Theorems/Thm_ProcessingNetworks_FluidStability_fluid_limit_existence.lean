-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidStability_fluid_limit_existence
-- name    : ProcessingNetworks.FluidStability.fluid_limit_existence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:37:30.060874+00:00
-- url     : https://prove2.me/theorems/bae208bf-5320-4be0-ac85-18ce36fb4612
-- title:
--   Theorem 6.5 — existence of fluid limits (milestone)
-- statement:
--   **Theorem 6.5 (existence of fluid limits).** Fix a sample point $\omega$ at which the SLLNs
--   (2.14) (for external arrivals) and (2.15) (for processing variables) and the negligibility
--   condition (6.38) all hold. For any unbounded set $C \subset \mathcal X$ of initial states,
--   there is a sequence $\{x_n\} \subset C$ with $|x_n| \to \infty$ such that
--   $$
--   \big(\hat D^{x_n}, \hat F^{x_n}, \hat T^{x_n}, \hat Z^{x_n}\big)(\cdot,\omega)
--   \ \xrightarrow{\text{u.o.c.}}\ (\hat D, \hat F, \hat T, \hat Z)
--   \quad \text{as } n \to \infty,
--   $$
--   for some $\hat F, \hat T \in C([0,\infty),\mathbb{R}^J)$ and $\hat D, \hat Z \in
--   C([0,\infty),\mathbb{R}^I)$; furthermore, $(\hat D, \hat F, \hat T, \hat Z)$ satisfies the
--   fluid equations (6.1)-(6.6) with $|\hat Z(0)| = 1$.
--
--   This is what makes fluid limit paths (Definition 6.6) a nonempty, well-behaved family: not
--   only do they exist along every unbounded sequence of initial states, but every one of them is
--   automatically a fluid model solution, which is the bridge Theorem 6.2 needs.
--
--   **Formalization note.** $|\hat Z(0)| = 1$ is a normalization coming from the choice of
--   scaling sequence, not an added restriction on the SPN — it is stated here as part of the
--   conclusion, exactly as the book states it. `Continuous Dh ∧ Continuous Fh ∧ Continuous Th ∧
--   Continuous Zh` makes explicit the theorem's own "$\hat F, \hat T \in C(\mathbb{R}_+,
--   \mathbb{R}^J)$ and $\hat D, \hat Z \in C(\mathbb{R}_+,\mathbb{R}^I)$" clause. The SLLNs
--   (2.14), (2.15) and the condition (6.38) are hypotheses on the fixed sample point $\omega$, for
--   the core stochastic elements $E, v, \varphi$ that the standard setup `SPNProcessFamily` is
--   built from; the fluid equations (6.1)–(6.6) for the limit follow from the system relations of
--   Section 2.5 satisfied by every version $x$ of the family.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 116, Theorem 6.5

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Theorem 6.5, Dai & Harrison p. 116 (PDF p. 132): fix `ω` such that the SLLNs (2.14), (2.15)
for the core stochastic elements and the negligibility condition (6.38) all hold. For any
unbounded set `C ⊂ 𝒳` of initial states, there is a sequence `{xₙ} ⊂ C` with `|xₙ| → ∞` such
that the fluid-scaled processes (6.37) converge u.o.c. to some continuous
`(D̂, F̂, T̂, Ẑ) ∈ C^I × C^J × C^J × C^I` (6.39), and furthermore `(D̂, F̂, T̂, Ẑ)` satisfies the
fluid equations (6.1)-(6.6) with `|Ẑ(0)| = 1`. -/
theorem fluid_limit_existence
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ) (ω : Ω)
    (C : Set Xstate) (hC : ¬ BddAbove ((spnSize Mrep) '' C))
    (h214 : ∀ i, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (dat.lam i)))
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)) ∧
        ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop
          (nhds (dat.Γ i j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0)) :
    ∃ (x : ℕ → Xstate) (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Dh ∧ Continuous Fh ∧ Continuous Th ∧ Continuous Zh ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.D (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Dh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * (fam.F (x n) (spnSize Mrep (x n) * t) ω j : ℝ)) Fh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Zh ∧
      IsFluidModelSolution dat Dh Fh Th Zh ∧ (∑ i, Zh 0 i) = 1 := by sorry

end ProcessingNetworks.FluidStability
