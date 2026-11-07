-- Prove2me | Theorems.Thm_PolySampIso_lemma_34
-- name    : PolySampIso.lemma_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:02.323207+00:00
-- url     : https://prove2.me/theorems/33d47eff-d795-4c6b-9074-2bb2b1fb7481
-- title:
--   Lemma 34, p.48 — one step of Algorithm 7 against the ideal proximal sampler
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $X$ be a nonempty bounded polytope with $m$ constraints in $\mathbb R^n$, $t\ge0$, $\tau,N\in\mathbb N$ with $N\ge Cn\tau$, and $K_\gamma$ the kernel of Algorithm 6. For bounded measurable $h:X\to\mathbb R$ let
--
--   $$(\tilde Ph)(x)=\mathbb E_{\Gamma\sim\pi^{\Gamma|X=x}_{t,\tau}}\big[(K_\Gamma h)(x)\big],\tag{64}$$
--
--   the one-step operator of Algorithm 7, and $\alpha_t=\max\{t,1/(16m)\}$. Then
--
--   $$\mathrm{Var}_{\pi_t}[\tilde Ph]\le\frac1{(1+\alpha_t/\tau)^2}\mathrm{Var}_{\pi_t}[h]+5\sqrt m\exp\Big(-\frac\tau{128}\Big)\mathrm{osc}(h)^2.$$
--
--   One step of the implementable sampler contracts variance at the rate of the ideal proximal sampler (Proposition 1 with the $\alpha_t$-$\psi$-PI of $\pi_t$), up to a defect that is exponentially small in $\tau$. Iterating it gives Proposition 8.
--
--   Differences from the source:
--   - encoding: there is a universal constant C > 0 → ∃ C > 0 chosen before m, n, A, b, t, τ, N, h; reason: universal means independent of every instance parameter
--   - encoding: bounded h : X → ℝ → measurable h : ℝⁿ → ℝ bounded on X; reason: standing measurability convention; values off X do not enter
--   - encoding: E_{Γ∼π^{Γ|X=x}_{t,τ}}[(K_Γh)(x)] → ∫ (K_γ h)(x) forwardsGammaLaw(x)(dγ), with forwardsGammaLaw the law of a sum of τ i.i.d. Exp(s(x)) vectors; reason: the Γ-conditional is the law of Algorithm 2's γ (Proposition 2, p.41)
--   - encoding: τ, N ∈ N → τ ≥ 1, N ≥ 1; reason: the paper's N starts at 1
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 34, p.48 (PDF p.50), eq. (64)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_MarkovKernel
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_Forwards
import Definitions.Def_PolySampIso_BackwardsMRW

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 34** (one step of Algorithm 7 against the ideal proximal sampler).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 34, p.48 (PDF p.50):

"Lemma 34. Let t ≥ 0, and let τ, N ∈ N, and let Kγ(x, ·) := Law (BackwardsMRW(x, γ, τ, t, N))
denote the Markov kernel corresponding to Algorithm 6. For all bounded h : X → R, define
(P̃h)(x) := EΓ∼πΓ|X=xt,τ [(KΓh)(x)] . (64) There is a universal constant C > 0 such that, if
N ≥ Cnτ, then for all bounded h : X → R,
Varπt[P̃h] ≤ 1/(1 + αt/τ)² Varπt[h] + 5√m exp(−τ/128) osc(h)², for αt := max{t, 1/(16m)}."

**Formalization Note.** `C` is chosen before all instance data. `K_γ = backwardsMRW A b γ τ t N`,
`π^{Γ|X=x}_{t,τ} = forwardsGammaLaw A b τ x`, so `(P̃h)(x) = ∫ (K_γ h)(x) π^{Γ|X=x}_{t,τ}(dγ)`;
`π_t = cooled A b t` (43). `Var` and `osc` are under `π_t`; `h` is bounded on `X` and measurable.
`τ, N ∈ N` are `≥ 1`; `t = 0` is allowed (`π_0 = π`). The standing assumption of §2.3 is kept. -/
theorem lemma_34 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), StandingAssumption A b →
        0 < n → ∀ t : ℝ, 0 ≤ t → ∀ τ N : ℕ, 1 ≤ τ → 1 ≤ N → C * n * τ ≤ N →
        ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, Measurable h →
          (∃ M, ∀ x ∈ polytope A b, |h x| ≤ M) →
          let Ptilde : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
            ∫ γ, kapply (backwardsMRW A b γ τ t N) h x ∂(forwardsGammaLaw A b τ x)
          let αt : ℝ := max t (1 / (16 * m))
          variance Ptilde (cooled A b t) ≤
            1 / (1 + αt / τ) ^ 2 * variance h (cooled A b t) +
              5 * Real.sqrt m * Real.exp (-(τ : ℝ) / 128) * osc h (cooled A b t) ^ 2 := by sorry

end PolySampIso
