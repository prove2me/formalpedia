-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidEquations_relaxed_policy_fluid_equation_corrected
-- name    : ProcessingNetworks.FluidEquations.relaxed_policy_fluid_equation_corrected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:40:20.826255+00:00
-- url     : https://prove2.me/theorems/54e7be18-d410-4f9b-a018-61107e5f7033
-- title:
--   Theorem 7.8 (relaxed-policy fluid equation), with $h \ge 0$ and measurable job counts
-- statement:
--   This is Theorem 7.8 of Dai and Harrison (the fluid equation for a relaxed control policy), stated with two conventions the book uses implicitly: the policy function takes values in $\mathbb R^I_+$, and the job-count processes are measurable in time.
--
--   Consider a unitary network, with one service type per class, and model data $(A,b)$. It operates under the relaxed control policy $\beta=h(\hat z)$ of (7.18). Here $h:\mathbb R^I_+\to\mathbb R^I_+$ has the following properties:
--
--   1. it is nonnegative and satisfies the capacity constraint $Ah(z)\le b$ for every $z\ge 0$ (7.19);
--   2. each component $h_i$ is continuous at every $z\ge0$ with $z_i>0$;
--   3. it is homogeneous of degree $0$: $h(cz)=h(z)$ for $c>0$ (Assumption 7.6).
--
--   On every sample path the cumulative effort is $T^x(t)=\int_0^t h(Z^x(u))\,du$, and $u\mapsto Z^x(u,\omega)$ is measurable.
--
--   Then every fluid limit path $(\hat D,\hat F,\hat T,\hat Z)$ satisfies (7.21): for each class $i$ and each $t>0$,
--   $$
--   \hat Z_i(t)>0\quad\Longrightarrow\quad \frac{d}{dt}\hat T_i(t)=h_i\big(\hat Z(t)\big).
--   $$
--
--   The result specializes to the non-idling and static-buffer-priority fluid equations, and it covers continuously varying relaxed policies such as proportionally fair allocation.
--
--   **Formalization Note.** This statement adds two hypotheses to the milestone `ProcessingNetworks.FluidEquations.relaxed_policy_fluid_equation`. The first is `hnonneg`, nonnegativity of $h$ on $\mathbb R^I_+$, as in the book's $h:\mathbb R^I_+\to\mathbb R^I_+$. The second is `hZmeas`, measurability of $u\mapsto Z^x(u,\omega)$; in the book this holds because $Z^x$ is piecewise constant. Without them the Bochner integral in `hpolicy` may be that of a non-measurable or unbounded integrand, so the milestone as stated cannot be proved. All other hypotheses and the conclusion are verbatim.
-- source:
--   J. G. Dai and J. M. Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, http://spnbook.org — Theorem 7.8, p. 132 (PDF p. 148), Eqs. (7.18)-(7.21), Assumption 7.6.

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_SatisfiesAssumption76

namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

theorem relaxed_policy_fluid_equation_corrected
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (sd : SPNData I I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep sd E v φ)
    (h : (Fin I → ℝ) → (Fin I → ℝ))
    (h719 : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → ∀ k, ∑ i, sd.A k i * h z i ≤ sd.b k)
    (h76 : SatisfiesAssumption76 h)
    (hnonneg : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → ∀ i, 0 ≤ h z i)
    (hZmeas : ∀ (x : Xstate) (ω : Ω), Measurable fun u => fam.Zx x u ω)
    (hpolicy : ∀ (x : Xstate) (ω : Ω) (t : ℝ), 0 ≤ t →
      fam.T x t ω = fun i => ∫ u in Set.Ioc (0 : ℝ) t, h (fun l => (fam.Zx x u ω l : ℝ)) i)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (i : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < Zh t i) :
    HasDerivAt (fun s => Th s i) (h (Zh t) i) t := by sorry

end ProcessingNetworks.FluidEquations
