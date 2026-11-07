-- Prove2me | Theorems.Thm_RobustKellyTV_theorem_3_2
-- name    : RobustKellyTV.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:52.787723+00:00
-- url     : https://prove2.me/theorems/e2522b2c-8a5f-46d6-848b-72644497066a
-- title:
--   Theorem 3.2 — small-gap sample complexity of $M^{\mathrm F}$: validity, (28) with an absolute constant, (29), and $M^{\mathrm F}_n\to\infty$ a.s.
-- statement:
--   Assume the standing assumptions. Then:
--
--   1. $M^{\mathrm F}$ is a test supermartingale under $\mathcal P_0$.
--   2. There is an absolute constant $C$ such that for every $d$, every setting $(P,\epsilon_0)$, every $S\in\Delta_d\setminus\mathcal P_0$ and every $\alpha\in(0,1)$,
--   $$\mathbb E_S\tau_\alpha(M^{\mathrm F})\le\frac{C}{\Delta(S)^2}\Big[d+\log(1/\alpha)+\ell(\Delta(S)^2)\Big].$$
--   3. For every setting there is $C_{P,\epsilon_0,d}<\infty$ such that for every $S\notin\mathcal P_0$ with $0<\Gamma(S)\le1$ and every $\alpha\in(0,1)$,
--   $$\mathbb E_S\tau_\alpha(M^{\mathrm F})\le\frac{C_{P,\epsilon_0,d}}{\Gamma(S)}\Big[d+\log(1/\alpha)+\ell(\Gamma(S))\Big].$$
--   4. $M^{\mathrm F}_n\to\infty$ almost surely under every $S\in\Delta_d\setminus\mathcal P_0$.
--
--   The alternatives may have zero coordinates. For fixed $\alpha$ this is the Farrell order $\Gamma(S)^{-1}\log\log(1/\Gamma(S))$.
--
--   Differences from the source:
--   - encoding: test supermartingale under P0 → M_0 = 1, M ≥ 0, and a supermartingale for the prefix filtration under every i.i.d. law R^∞ with R ∈ P0; reason: the paper's reading in the proofs of Theorems 2.5 and 3.2 (pp.23, 29)
--   - encoding: i.i.d. observations X_1, X_2, … from S → the infinite product law of S on ℕ → Fin d, with X_t the coordinate t − 1; reason: every process is a function of the observed prefix, so no instance changes
--   - encoding: E_S τ → a lintegral of τ (valued in ℕ∞) in [0, ∞]; reason: an infinite expectation is kept as ∞ and cannot read as 0
--   - encoding: an absolute constant C → ∃ C quantified before d and the setting (P, ϵ0); reason: absolute means independent of d, P, ϵ0, S and α
--   - reading: M^F_n → ∞ almost surely under every such S → under every S ∈ ∆_d \ P0; reason: the broader reading; the proof (p.31) argues for every S ∉ P0
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §3.2, Theorem 3.2, eqs. (28)–(29), p.12 (proof pp.29–31)

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_seqLaw
import Definitions.Def_RobustKellyTV_MF

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustKellyTV

/-- **Theorem 3.2** (Small-gap sample complexity). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Theorem 3.2, eqs. (28)–(29), p.12.

The process `M^F` is a test supermartingale under `P0`. There is an absolute constant `C` such that,
for every `S ∉ P0` and `α ∈ (0, 1)`, `E_S τ_α(M^F) ≤ C/∆(S)² [d + log(1/α) + ℓ(∆(S)²)]` (28).
Consequently, for `0 < Γ(S) ≤ 1`, `E_S τ_α(M^F) ≤ C_{P,ϵ0,d}/Γ(S) [d + log(1/α) + ℓ(Γ(S))]` (29),
where `C_{P,ϵ0,d} < ∞` depends only on the fixed null geometry. Also, `M^F_n → ∞` almost surely
under every such `S`.

**Formalization Note.** Four conjuncts. The constant `C` of (28) is absolute: it is chosen before
`d` and the setting `σ` (standing assumptions of p.6). The constant of (29) is chosen after the
setting and before `S` and `α`. `S ∉ P0` may have zero coordinates. `E_S τ` is a `lintegral` in
`[0, ∞]`. The divergence clause is stated for every `S ∈ ∆_d \ P0`. -/
theorem theorem_3_2 :
    (∀ (d : ℕ) (σ : Setting d), IsTestSupermartingale σ (MF σ)) ∧
    (∃ C : ℝ, ∀ (d : ℕ) (σ : Setting d) (S : stdSimplex ℝ (Fin d)),
      (S : Fin d → ℝ) ∉ nullBall σ → ∀ α : ℝ, 0 < α → α < 1 →
        ∫⁻ ω, (stopTime (MF σ) α ω : ℝ≥0∞) ∂(seqLaw S) ≤
          ENNReal.ofReal (C / gap σ S ^ 2 *
            ((d : ℝ) + Real.log (1 / α) + ell (gap σ S ^ 2)))) ∧
    (∀ (d : ℕ) (σ : Setting d), ∃ C : ℝ, ∀ S : stdSimplex ℝ (Fin d),
      (S : Fin d → ℝ) ∉ nullBall σ → 0 < Gamma σ S → Gamma σ S ≤ 1 →
        ∀ α : ℝ, 0 < α → α < 1 →
          ∫⁻ ω, (stopTime (MF σ) α ω : ℝ≥0∞) ∂(seqLaw S) ≤
            ENNReal.ofReal (C / Gamma σ S *
              ((d : ℝ) + Real.log (1 / α) + ell (Gamma σ S)))) ∧
    (∀ (d : ℕ) (σ : Setting d) (S : stdSimplex ℝ (Fin d)), (S : Fin d → ℝ) ∉ nullBall σ →
      ∀ᵐ ω ∂(seqLaw S), Tendsto (fun n : ℕ => MF σ n ω) atTop atTop) := by sorry

end RobustKellyTV
