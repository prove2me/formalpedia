-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidStability_fluid_limit_compactness
-- name    : ProcessingNetworks.FluidStability.fluid_limit_compactness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:35:56.858669+00:00
-- url     : https://prove2.me/theorems/b123bba6-d07f-4537-8f7a-81a3186524bb
-- title:
--   Lemma 6.7 — compactness of the scaled service-effort processes
-- statement:
--   **Lemma 6.7.** Fix a sample point $\omega$. For any unbounded set $C \subset \mathcal X$ of
--   initial states (i.e. $\{|x| : x \in C\}$ is unbounded), there is a sequence $\{x_n\} \subset
--   C$ with $|x_n| \to \infty$ such that $\hat T^{x_n}(\cdot,\omega) \to \hat T(\cdot)$ u.o.c. and
--   $\hat Z^{x_n}(0,\omega) \to \hat Z(0)$ as $n \to \infty$, for some
--   $\hat T \in C([0,\infty),\mathbb{R}^J)$ and some $\hat Z(0) \in \mathbb{R}^I_{\ge 0}$.
--
--   This is the first of the two convergence lemmas behind Theorem 6.5: it isolates convergence
--   of the (equicontinuous, by the capacity bound (6.6)) scaled service-effort process $\hat T^x$
--   and of the scaled initial buffer contents $\hat Z^x(0)$, via an Arzelà–Ascoli-type
--   compactness argument.
--
--   **Formalization note.** The sequence is required to lie in $C$ (`∀ n, x n ∈ C`), matching the
--   lemma's "there exists a sequence $\{x_n\} \subset C$" exactly; this is the one place besides
--   Theorem 6.5 itself where the arbitrary unbounded set $C$ (rather than all of $\mathcal X$)
--   matters. The convergence of $\hat Z^{x_n}(0,\omega) = Z^{x_n}(0)/|x_n|$ uses that
--   $Z^{x}(0)$ is the buffer-content part of $f(x)$ (a field of `SPNProcessFamily`), so that these
--   scaled initial contents lie in the unit simplex.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 116, Lemma 6.7

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Lemma 6.7, Dai & Harrison p. 116 (PDF p. 132): fix `ω`. For any unbounded set `C` of initial
states (unbounded meaning `{|x| : x ∈ C}` is unbounded in `ℝ`), there is a sequence `{xₙ} ⊂ C`
with `|xₙ| → ∞` such that `T̂^{xₙ}(·,ω) → T̂(·)` u.o.c. and `Ẑ^{xₙ}(0,ω) → Ẑ(0)` as `n → ∞`
(6.40), for some `T̂ ∈ C(ℝ≥0,ℝ^J)` and `Ẑ(0) ∈ ℝ^I_{≥0}`. -/
theorem fluid_limit_compactness
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω) (C : Set Xstate)
    (hC : ¬ BddAbove ((spnSize Mrep) '' C)) :
    ∃ (x : ℕ → Xstate) (Th : ℝ → Fin J → ℝ) (Zh0 : Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Th ∧ (∀ i, 0 ≤ Zh0 i) ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      Tendsto (fun n i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) 0 ω i : ℝ)) atTop (nhds Zh0) := by sorry

end ProcessingNetworks.FluidStability
