-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_Supplement_codebook_pulses
-- name    : TightReleaseSchedules.Stationary.Supplement.codebook_pulses
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:22:52.784312+00:00
-- url     : https://prove2.me/theorems/ca435728-90aa-45cc-b1d4-b13688c046e7
-- title:
--   Theorem 6.1 — codebook pulses under a release budget, risk at least Khδ²/512
-- statement:
--   The pretrained predictor is $\theta_0=0$. Let $d,B,K,N,h\ge1$ be integers, let $0<\delta\le1$, and let $u_1,\dots,u_M\in\mathbb R^d$ be a codebook with
--
--   $$
--   M\ge2,\qquad \|u_v\|_2\le\delta,\qquad \|u_v-u_{v'}\|_2>\delta/2\quad(v\ne v').
--   $$
--
--   Suppose further that
--
--   $$
--   1+KNh\le T,\qquad MKN\ge1024B,\qquad h\delta^2\le\frac18\log\frac{MKN}{4B}
--   $$
--
--   (natural logarithm). Observations follow the random-design model $X_t\sim N(0,I_d)$ and $Y_t=X_t^\top\theta_t+\xi_t$ with $\xi_t\sim N(0,1)$, all independent. Let $\mathcal H$ be the pulse family of the proof (phases of $N$ blocks of length $h$, at most one pulse $u_{V_p}$ per phase). Then:
--
--   1. Every path in $\mathcal H$ has $\theta_1=0$, $\|\theta_t\|_2\le\delta$, $\sum_{t=2}^{T}\|\theta_t-\theta_{t-1}\|_2\le2K\delta$, and at most $2K$ changes. If $2K\le B$, the path admits a zero-error piecewise-constant representation with the same budget: some policy with at most $B$ releases at dates fixed in advance (with knowledge of the path) deploys exactly $\theta_t$ in every round $t$.
--   2. Every randomized causal policy using at most $B$ releases has a deterministic path $\theta_{1:T}\in\mathcal H$ on which
--
--   $$
--   \frac12\,\mathbb E\sum_{t=1}^{T}\|w_t-\theta_t\|_2^2\ \ge\ \frac{Kh\delta^2}{512}.
--   $$
--
--   The policy may know the zero initial target and the codebook, and its memory and causal monitoring are unrestricted. The bound shows that the dimension (through $M$), the unknown change locations and the release quota enter one information threshold. Never releasing has risk at most $Kh\delta^2/2$ on this family, so the order $\Theta(Kh\delta^2)$ is exact on it.
--
--   **Formalization Note** Round $t$ is index $t-1$ of `Fin T`. The policy is quantified after the codebook, so it may depend on it, and the path is chosen after the policy. The deployed predictor and risk are those of the base mission with initial head $0$.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,T$, randomized causal policies with at most $B$ releases and expected half-squared risk → index $i$ of `Fin T` is round $i+1$, the base mission's `ReleasePolicy`/`IsCausal` on an arbitrary seed space, `ENNReal`-valued `policyRisk` compared with `ENNReal.ofReal` of the real bound; reason: the base mission's conventions, which change no instance and exclude no competitor with infinite risk.
--   - generalization: "a deterministic parameter path with $\theta_1=0$, $\|\theta_t\|_2\le\delta$, total variation $\le2K\delta$", and "every path in the hard family admits zero-error piecewise-constant representation using the same release budget, when its future changes are known" → the witness path is a member of the explicitly defined pulse family of proof Step 1 (p. 21). Every member of that family satisfies the norm and variation bounds and has at most $2K$ changes. When $2K\le B$, every member is exactly represented by a fixed-date $B$-slot policy; reason: the hard family is the one defined in the proof, and the Lean conclusion implies the source's existence of a path with the stated bounds.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Theorem 6.1, printed p.21, PDF p.22; proof printed pp.21–23, PDF pp.22–24; θ_0 = 0 standing assumption §6, printed p.21, PDF p.22

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_pulse_class

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- Theorem 6.1 (printed p. 21, PDF p. 22), with pretrained predictor `θ₀ = 0`. Every path of
the pulse family has `θ₁ = 0`, `‖θ_t‖₂ ≤ δ`, total variation at most `2Kδ`, at most `2K`
changes, and, when `2K ≤ B`, a zero-error representation by `B` releases at known dates.
For every causal randomized policy with at most `B` releases (which may depend on the
codebook) some path of the family has risk at least `Khδ²/512`. -/
theorem codebook_pulses (T d B K N h M : ℕ) (hd : 1 ≤ d) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hN : 1 ≤ N) (hh : 1 ≤ h) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (u : Fin M → Vector d) (hM : 2 ≤ M) (hu : ∀ v, ‖u v‖ ≤ δ)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖)
    (hTKNh : 1 + K * N * h ≤ T) (hMKN : 1024 * B ≤ M * K * N)
    (hinfo : (h : ℝ) * δ ^ 2 ≤ (1 / 8) * Real.log ((M * K * N : ℝ) / (4 * B))) :
    (∀ θ ∈ pulseFamily T d K N M h u,
        (∀ i : Fin T, i.val = 0 → θ i = 0) ∧
        (∀ i, ‖θ i‖ ≤ δ) ∧
        totalVariation θ ≤ 2 * K * δ ∧
        changeCount θ ≤ 2 * K ∧
        (2 * K ≤ B → ∃ π' : ReleasePolicy unitSeed T d B,
          IsCausal π' ∧ HasDeterministicDates π' ∧ ∀ ω i, deployed 0 π' ω i = θ i)) ∧
    (∀ (s : RandomSeed) (π : ReleasePolicy s T d B), IsCausal π →
      ∃ θ ∈ pulseFamily T d K N M h u,
        ENNReal.ofReal ((K : ℝ) * h * δ ^ 2 / 512) ≤ policyRisk 0 π θ) := by sorry

end TightReleaseSchedules.Stationary.Supplement
