-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidEquations_relaxed_policy_fluid_equation
-- name    : ProcessingNetworks.FluidEquations.relaxed_policy_fluid_equation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:49:46.342792+00:00
-- url     : https://prove2.me/theorems/cf8339ef-3fde-42fa-a7b0-d9fefdbb19df
-- title:
--   Theorem 7.8 — fluid equation for a general relaxed control policy (milestone)
-- statement:
--   Consider a **unitary network** (Section 2.6, one service type per class) operating under a
--   relaxed control policy of the form $\beta = h(\hat z)$ (7.18), where $\hat z$ is the updated
--   job-count vector and $h : \mathbb{R}^I_+ \to \mathbb{R}^I_+$ satisfies the capacity
--   constraint $Ah(z) \le b$ for all $z \ge 0$ (7.19) and is continuous away from $0$ and
--   homogeneous of degree $0$ (Assumption 7.6).
--
--   **Theorem 7.8.** Each fluid limit path $(\hat D, \hat F, \hat T, \hat Z)$ satisfies (7.21):
--   for each class $i$ and $t > 0$,
--   $$
--   \hat Z_i(t) > 0 \quad\Longrightarrow\quad \frac{d}{dt}\hat T_i(t) = h_i(\hat Z(t)).
--   $$
--
--   This is a genuine generalization of Theorems 7.2/7.3: any non-idling or SBP policy for a
--   unitary network can be written in the form $\beta = h(\hat z)$ for a suitable homogeneous
--   $h$, and Theorem 7.8 recovers their fluid equations as special cases while also covering
--   continuously-varying relaxed policies (e.g. the proportionally fair allocation of Chapters
--   9-10) that Theorems 7.2/7.3 do not directly address.
--
--   **Formalization note.** The policy is formalized via `hpolicy`, the raw sample-path identity
--   $T^x(t,\omega) = \int_0^t h(Z^x(u,\omega))\,du$ that (2.28) ($T_i(t) = \int_0^t \beta_i(u)du$)
--   together with $\beta = h(\hat z)$ (7.18) gives directly — exact, since the updated job count
--   $\hat z$ coincides with $Z^x(u)$ except at the decision times, a null set of $u$. The unitary
--   network's model data `sd` (mission I's `SPNData`, with $J = I$) supply the $A$ and $b$ of the
--   capacity constraint (7.19), and the standard setup's $Z^x$ is integer-valued, hence nonnegative,
--   so $h$ is only ever evaluated on $\mathbb{R}^I_+$, where Assumption 7.6 constrains it. As
--   Remark 7.9 warns, the converse statement ($\hat Z_i(t) = 0 \Rightarrow d/dt\,\hat T_i(t) = 0$)
--   is *not* asserted here and need not hold (a corrected version is Lemma 8.9, out of scope for
--   this mission).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 132, Theorem 7.8

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_SatisfiesAssumption76

namespace ProcessingNetworks.FluidEquations

open MeasureTheory ProcessingNetworks.Stability

/-- Theorem 7.8, Dai & Harrison p. 132 (PDF p. 148): consider a unitary network (model data `sd`
with `J = I`) operating under the relaxed control policy `β = h(ẑ)` of (7.18), where
`h : ℝ^I_+ → ℝ^I_+` satisfies the capacity constraint `A h(z) ≤ b` for every `z ≥ 0` (7.19) and
Assumption 7.6. Each fluid limit path `(D̂, F̂, T̂, Ẑ)` satisfies (7.21): for each class `i` and
`t > 0`, `Ẑᵢ(t) > 0` implies `d/dt T̂ᵢ(t) = hᵢ(Ẑ(t))`. The policy itself is recorded by
`hpolicy`, the sample-path identity `T^x(t) = ∫₀ᵗ h(Z^x(u)) du` that (2.28) together with
`β = h(ẑ)` (7.18) gives (the updated job count `ẑ` equals `Z^x(u)` except at the decision times,
a null set of `u`). -/
theorem relaxed_policy_fluid_equation
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (sd : SPNData I I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep sd E v φ)
    (h : (Fin I → ℝ) → (Fin I → ℝ))
    (h719 : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → ∀ k, ∑ i, sd.A k i * h z i ≤ sd.b k)
    (h76 : SatisfiesAssumption76 h)
    (hpolicy : ∀ (x : Xstate) (ω : Ω) (t : ℝ), 0 ≤ t →
      fam.T x t ω = fun i => ∫ u in Set.Ioc (0 : ℝ) t, h (fun l => (fam.Zx x u ω l : ℝ)) i)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (i : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < Zh t i) :
    HasDerivAt (fun s => Th s i) (h (Zh t) i) t := by sorry

end ProcessingNetworks.FluidEquations
