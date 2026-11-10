-- Prove2me | Theorems.Thm_ThinShellSampling_lemma_6_2
-- name    : ThinShellSampling.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:26.593961+00:00
-- url     : https://prove2.me/theorems/05b3249f-1039-4dd3-b78d-b8c51852f191
-- title:
--   Lemma 6.2 — moments of a logconcave measure with bounded density ratio
-- statement:
--   Let $\pi,\bar\pi$ be probability measures on $\mathbb R^n$ with $\bar\pi$ logconcave and $d\bar\pi/d\pi\le p_0^{-1}$ for some $p_0>0$, and let $\pi$ have a finite second moment. Write $R,L,\Lambda,\Sigma$ for the parameters of $\pi$ and $\bar R,\bar L,\bar\Lambda$ for those of $\bar\pi$. There is a universal constant $C$ such that:
--
--   1. $\mathbb E_{\bar\pi}[XX^{\mathsf T}]\preceq p_0^{-1}\mathbb E_\pi[XX^{\mathsf T}]$ and $\operatorname{cov}_{\bar\pi}X\preceq p_0^{-1}\Sigma$;
--   2. $\bar R^2\le p_0^{-1}R^2$, $\bar L\le p_0^{-1}L$ and $\bar\Lambda\le p_0^{-1}\Lambda$;
--   3. $\displaystyle\sup_{\sigma^2>0}\operatorname{Var}_{\bar\pi_{\sigma^2}}(\|X\|^2)\le C\,p_0^{-2}\big(R^2L\wedge R^3\sqrt\Lambda\big)$, where $\bar\pi_{\sigma^2}$ is the Gaussian tilt of $\bar\pi$.
--
--   Applied to the truncated lift ($p_0=1/2$), it shows that the thin-shell input $\bar{\mathcal V}$ of Algorithm 6.6 is within a universal factor of $R^2L\wedge R^3\sqrt\Lambda$.
--
--   **Formalization Note** $d\bar\pi/d\pi\le p_0^{-1}$ is the measure inequality $\bar\pi\le p_0^{-1}\pi$; $\preceq$ is the Loewner order.
--
--   Differences from the source:
--
--   - generalization: π̄ logconcave (full-dimensional, §1.3) → the published FunctionalInequalities.KLS.LogConcave, admitting degenerate supports; reason: includes every full-dimensional logconcave π̄; footnote 5, p.12
--   - encoding: no moment hypothesis on π → MemLp id 2 π; reason: if E_π‖X‖² = ∞ then R, L, Λ are infinite and every bound is vacuous; the hypothesis only excludes that case
--   - encoding: ≲ in the third item → a universal constant C > 0, chosen before n, π, π̄, p₀; reason: the paper's convention (§1.3, p.12)
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Lemma 6.2, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_covMat

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Lemma 6.2 (comparison of moments under a bounded density ratio).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Lemma 6.2, p.36 (PDF p.38): "Let `π` and `π̄` be probability measures on `ℝⁿ` such that `π̄` is
logconcave, and `dπ̄/dπ ≤ p₀⁻¹` for some `p₀ > 0`. Let `R̄, L̄, Λ̄` denote the analogues of `R, L, Λ` for
`π̄`. Then: `E_π̄[XXᵀ] ⪯ p₀⁻¹ E_π[XXᵀ]` and `cov_π̄ X ⪯ p₀⁻¹ Σ`; `R̄² ≤ p₀⁻¹R²`, `L̄ ≤ p₀⁻¹L`, and
`Λ̄ ≤ p₀⁻¹Λ`; `sup_{σ²>0} Var_{π̄_{σ²}}(‖X‖²) ≲ p₀⁻² (R²L ∧ R³√Λ)`."

**Formalization Note.**
* `dπ̄/dπ ≤ p₀⁻¹` is the measure inequality `π̄ ≤ p₀⁻¹ • π`. `⪯` is the Loewner order
  (`(p₀⁻¹ A − B).PosSemidef`).
* `π` is assumed to have a finite second moment (`MemLp id 2 π`): otherwise `R, L, Λ` are infinite
  and every bound is vacuous in the paper; the hypothesis only excludes that undefined case.
* `≲` in the third item is a universal constant `C`, chosen before `n, π, π̄, p₀`.
* Logconcavity of `π̄` is the published `FunctionalInequalities.KLS.LogConcave` (also admitting
  degenerate supports; see Theorem 1.4). -/
theorem lemma_6_2 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (π : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure π]
      (πb : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (p₀ : ℝ),
      FunctionalInequalities.KLS.LogConcave πb → 0 < p₀ →
      (πb : Measure (EuclideanSpace ℝ (Fin n))) ≤ ENNReal.ofReal p₀⁻¹ • π →
      MemLp id 2 π →
      let μb : Measure (EuclideanSpace ℝ (Fin n)) := πb
      ((p₀⁻¹ • secondMomentMat π - secondMomentMat μb).PosSemidef ∧
        (p₀⁻¹ • covMat π - covMat μb).PosSemidef) ∧
      (rsq μb ≤ p₀⁻¹ * rsq π ∧ Lmom μb ≤ p₀⁻¹ * Lmom π ∧ Lam μb ≤ p₀⁻¹ * Lam π) ∧
      (⨆ σ2 : ℝ, ⨆ (_ : 0 < σ2), evariance (fun x => ‖x‖ ^ 2) (gaussTilt μb σ2)) ≤
        ENNReal.ofReal (C * p₀⁻¹ ^ 2 *
          min (rsq π * Lmom π) (Real.sqrt (rsq π) ^ 3 * Real.sqrt (Lam π))) := by sorry

end ThinShellSampling
