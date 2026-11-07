-- Prove2me | Theorems.Thm_PolySampIso_lemma_30
-- name    : PolySampIso.lemma_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:24.811982+00:00
-- url     : https://prove2.me/theorems/7089b97e-ed7b-4c09-8628-c1d06e0cc6fc
-- title:
--   Lemma 30, p.42 — the dual-stable set carries most of the backwards mass on average
-- statement:
--   Let $X$ be a nonempty bounded polytope with $m$ constraints, $t\ge0$ and $\tau\in\mathbb N$. Draw $x\sim\pi_t$, then $\gamma\sim\pi^{\Gamma|X=x}_{t,\tau}$ (the sum of $\tau$ i.i.d. $\mathrm{Exp}(s(x))$ vectors). Then
--
--   $$\mathbb E_{\gamma\sim\pi^\Gamma_{t,\tau}}\Big[\pi^{X|\Gamma=\gamma}_{t,\tau}\big(B_\tau(\gamma,\tfrac14)\big)\Big]\ge1-2m\exp\Big(-\frac\tau{64}\Big),$$
--
--   where $\pi^\Gamma_{t,\tau}=\mathbb E_{x\sim\pi_t}[\pi^{\Gamma|X=x}_{t,\tau}]$ and $B_\tau(\gamma,\tfrac14)=\{x\in X:|1-\gamma_is_i(x)/\tau|\le\tfrac14\ \forall i\}$.
--
--   The backwards conditional measures are well conditioned only on $B_\tau(\gamma,\tfrac14)$; this lemma says that the mass outside it is small on average over $\gamma$, which is the defect that Lemma 34 has to absorb. It is what lets the step size be as small as $\tau=O(\log(m/\delta))$.
--
--   Differences from the source:
--   - encoding: E_{γ∼π^Γ_{t,τ}}[·] with π^Γ_{t,τ} := E_{x∼π_t}[π^{Γ|X=x}_{t,τ}] → the iterated integral ∫ π_t(dx) ∫ π^{Γ|X=x}_{t,τ}(dγ) [·], computed in [0, ∞] with the bound clamped at 0; reason: the paper's definition of π^Γ on p.41; the bound is trivial where it is negative
--   - encoding: τ ∈ N → τ ≥ 1; reason: the paper's N starts at 1
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 30, p.42 (PDF p.44); π^Γ defined p.41

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_Forwards
import Definitions.Def_PolySampIso_DualConditioning

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 30** (the dual-stable set has large backwards mass on average).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 30, p.42 (PDF p.44):

"Lemma 30. For all t ≥ 0 and τ ∈ N, Eγ∼πΓt,τ[πX|Γ=γt,τ(Bτ(γ, 1/4))] ≥ 1 − 2m exp(−τ/64)."

**Formalization Note.** `π^Γ_{t,τ} := E_{x∼π_t}[π^{Γ|X=x}_{t,τ}]` (p.41), so the expectation is the
iterated integral `∫ π_t(dx) ∫ π^{Γ|X=x}_{t,τ}(dγ) π^{X|Γ=γ}_{t,τ}(B_τ(γ, ¼))`, with
`π^{Γ|X=x}_{t,τ} = forwardsGammaLaw A b τ x` (the law of a sum of `τ` i.i.d. `Exp(s(x))` vectors),
`π^{X|Γ=γ}_{t,τ} = condX A b t τ γ` (55) and `B_τ = stableSet` (57). It is computed in `ℝ≥0∞`
(the right side of the paper's bound is clamped at `0` by `ENNReal.ofReal`, where it is trivial).
`τ ∈ N` is `τ ≥ 1`; the standing assumption of §2.3 is kept. -/
theorem lemma_30 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) (τ : ℕ) (hτ : 1 ≤ τ) :
    ENNReal.ofReal (1 - 2 * m * Real.exp (-(τ : ℝ) / 64)) ≤
      ∫⁻ x, ∫⁻ γ, condX A b t τ γ (stableSet A b τ γ (1 / 4)) ∂(forwardsGammaLaw A b τ x)
        ∂(cooled A b t) := by sorry

end PolySampIso
