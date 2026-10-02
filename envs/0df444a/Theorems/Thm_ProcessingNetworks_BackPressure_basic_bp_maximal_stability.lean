-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_basic_bp_maximal_stability
-- name    : ProcessingNetworks.BackPressure.basic_bp_maximal_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:00:55.784984+00:00
-- url     : https://prove2.me/theorems/af22e0da-f9a9-49cc-8b50-65e88d6b32d2
-- title:
--   Theorem 9.13 — maximal stability of basic back-pressure (milestone)
-- statement:
--   **Theorem 9.13.** Consider a Leontief network operating under the *basic* back-pressure
--   policy, with $b_k=1$ for every pool and each column of $A$ a single $1$ (every activity uses
--   exactly one server, alone). If $\gamma^*<1$, the fluid limit is stable.
--
--   This does *not* follow automatically from Theorem 9.12: the basic model's discrete, "one
--   service at a time" dynamics need a genuinely different argument (via Lemma 9.14's residual-time
--   SLLN) to show the fluid limit still satisfies the characteristic equation (9.22) — the basic
--   and relaxed policies coincide at the fluid level only under these extra single-server
--   hypotheses.
--
--   **Formalization note.** As the book's proof says, "it will suffice to show that the fluid
--   equation (9.22) remains valid under the basic BP policy", so the theorem is stated for a fluid
--   limit path $(\hat D, \hat F, \hat T, \hat Z, \hat Y)$ of the basic-BP network, given by its raw
--   processes and their fluid-scaled convergences along $(\omega, \{x_n\})$, in the form of Lemma
--   9.11: the basic policy's allocations are drawn from $N = \{\beta \in \mathbb{Z}^J_+ : A\beta
--   \le e\}$; $T = \sum_\beta \beta Y_\beta$, $Y_\beta$ nondecreasing, $\sum_\beta Y_\beta(t) = t$;
--   and the operational content of the basic BP rule is the bound (9.54): if $\beta$ is strictly
--   dominated throughout a raw time interval by an allocation $\beta^*$ that is feasible for
--   (9.15)–(9.17) whenever $\beta$ is ((9.47)–(9.48)), then $\beta$ accrues over that interval at
--   most the residual service time of the activity in progress plus the residual inter-arrival
--   time (the wait until the next decision time). Lemma 9.14's conclusion — that these residual
--   times are negligible under the fluid scaling along the sequence — is the hypothesis
--   `hres_v`/`hres_u`. `hb1` and `hA01` are the two extra structural hypotheses the book states,
--   per this mission's own `BRIEF.md` warning that they are genuinely additional structure. The
--   conclusion is the pair the proof establishes: the path is a solution of the relaxed-BP fluid
--   model (it satisfies (9.22)), and that model is stable (Theorem 9.12), so the fluid limit is
--   stable.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 178, Theorem 9.13

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_RegularPoint
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

namespace ProcessingNetworks.BackPressure

open MeasureTheory Filter

/-- Theorem 9.13, Dai & Harrison p. 178 (PDF p. 194): consider a Leontief network operating
under the basic back-pressure control policy, with `b_k = 1` for every pool `k` and each column
of `A` containing a single `1` and the rest zeros (every activity uses one server, acting alone —
the extra structural hypotheses Lemma 9.14's proof needs, genuinely beyond "basic vs. relaxed").
If the static planning problem has optimal objective value `γ* < 1`, the corresponding fluid
limit is stable. As the book's proof says, "it will suffice to show that the fluid equation (9.22)
remains valid under the basic BP policy": the theorem is stated for a fluid limit path
`(D̂, F̂, T̂, Ẑ, Ŷ)` of the basic-BP network, given by its raw processes and their fluid-scaled
convergences (6.39)/(9.32) along `(ω, xₙ)`, with the basic policy's allocations drawn from
`N = {β ∈ ℤ^J_+ : Aβ ≤ e}` and the operational content of the basic BP rule recorded as the
bound (9.54): if an allocation `β` is strictly dominated throughout a raw time interval by an
allocation `β*` that is feasible (9.16)–(9.17) whenever `β` is ((9.47)–(9.48)), then `β` accrues
over that interval at most the residual service time of the activity in progress plus the residual
inter-arrival time (the wait until the next decision time), whose fluid-scaled negligibility is
Lemma 9.14. The conclusion is that the path satisfies (9.22) — it is a solution of the relaxed-BP
fluid model — together with the stability of that model (Theorem 9.12), hence the fluid limit is
stable. -/
theorem basic_bp_maximal_stability
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    (dat : SPNPlanningData I J K) (hleontief : IsLeontiefNetwork dat)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (hb1 : ∀ k : Fin K, dat.b k = 1)
    (hA01 : ∀ j : Fin J, ∃! k : Fin K, dat.A k j = 1 ∧ ∀ k' : Fin K, k' ≠ k → dat.A k' j = 0)
    (lam : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (γstar : ℝ) (hopt : IsOptimalSPPValue dat lam γstar) (hsub : γstar < 1)
    (N : Finset (Fin J → ℝ))
    (hN : ∀ β : Fin J → ℝ, β ∈ N ↔ (∀ j, β j = 0 ∨ β j = 1) ∧ ∀ k, ∑ j, dat.A k j * β j ≤ 1)
    (Nraw : Xstate → ℝ → Ω → Fin J → ℕ) (Zraw : Xstate → ℝ → Ω → Fin I → ℕ)
    (Traw : Xstate → ℝ → Ω → Fin J → ℝ) (Yraw : (Fin J → ℝ) → Xstate → ℝ → Ω → ℝ)
    (vhat : Fin J → Xstate → ℝ → Ω → ℝ) (uhat : Fin I → Xstate → ℝ → Ω → ℝ)
    (size : Xstate → ℝ) (size_nonneg : ∀ x, 0 ≤ size x)
    (hTY : ∀ x ω t j, Traw x t ω j = ∑ β ∈ N, β j * Yraw β x t ω)
    (hYmono : ∀ β ∈ N, ∀ x ω, Monotone (Yraw β x · ω))
    (hYsum : ∀ x ω t, 0 ≤ t → ∑ β ∈ N, Yraw β x t ω = t)
    (hBP : ∀ β ∈ N, ∀ βstar ∈ N, ∀ (x : Xstate) (ω : Ω) (u1 u2 : ℝ), 0 ≤ u1 → u1 ≤ u2 →
      (∀ u ∈ Set.Icc u1 u2,
        p dat β (fun i => (Zraw x u ω i : ℝ)) < p dat βstar (fun i => (Zraw x u ω i : ℝ))) →
      (∀ u ∈ Set.Icc u1 u2,
        BPFeasible dat (Nraw x u ω) (Zraw x u ω) β → BPFeasible dat (Nraw x u ω) (Zraw x u ω) βstar) →
      Yraw β x u2 ω - Yraw β x u1 ω ≤ (⨆ j, vhat j x u1 ω) + (⨅ i, uhat i x u1 ω))
    (ω : Ω) (x : ℕ → Xstate) (hsize : Tendsto (fun n => size (x n)) atTop atTop)
    (hres_v : ∀ (j : Fin J) (s : ℝ), 0 < s →
      Tendsto (fun n => (size (x n))⁻¹ * vhat j (x n) (size (x n) * s) ω) atTop (nhds 0))
    (hres_u : ∀ (i : Fin I) (s : ℝ), 0 < s →
      Tendsto (fun n => (size (x n))⁻¹ * uhat i (x n) (size (x n) * s) ω) atTop (nhds 0))
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) (Yh : (Fin J → ℝ) → ℝ → ℝ)
    (hsol : IsFluidModelSolution dat lam Dh Fh Th Zh)
    (hZconv :
      UOCConverges (fun n t i => (size (x n))⁻¹ * (Zraw (x n) (size (x n) * t) ω i : ℝ)) Zh)
    (hTconv :
      UOCConverges (fun n t j => (size (x n))⁻¹ * Traw (x n) (size (x n) * t) ω j) Th)
    (hYconv : ∀ β ∈ N,
      UOCConvergesR (fun n t => (size (x n))⁻¹ * Yraw β (x n) (size (x n) * t) ω) (Yh β)) :
    IsRelaxedBPFluidSolution dat lam Dh Fh Th Zh ∧ RelaxedBPFluidStable dat lam := by sorry

end ProcessingNetworks.BackPressure
