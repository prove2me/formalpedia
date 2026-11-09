-- Prove2me | Theorems.Thm_PhiSobBayes_fact_A_22
-- name    : PhiSobBayes.fact_A_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:15.581867+00:00
-- url     : https://prove2.me/theorems/b05987c2-5661-418a-98e4-91c2794aa8d1
-- title:
--   Fact A.22 (Bakry–Émery) — $\nabla^2W\succeq\rho I_n$ gives $C_{\mathrm P},C_{\mathrm{LS}}\le1/\rho$ and every $\Phi$-Sobolev inequality with constant $1/\rho$
-- statement:
--   Let $\mu(dx)=e^{-W(x)}\,dx$ be a probability measure on $\mathbb R^n$ with $\nabla^2W\succeq\rho I_n$ for some $\rho>0$. Then
--
--   1. $C_{\mathrm P}(\mu)\le1/\rho$,
--   2. $C_{\mathrm{LS}}(\mu)\le1/\rho$, and
--   3. more generally, $\mu$ satisfies the $\Phi$-Sobolev inequality (1) with constant $1/\rho$ for every open interval $J$ and every $\Phi:J\to\mathbb R$ smooth with $\Phi''>0$ and $1/\Phi''$ concave.
--
--   This is a cited result ([BÉ85]; [Cha04, Corollary 2.1]). Applied to the posteriors of Lemma 6.1 with $\rho=t$, it gives the key inequality (49).
--
--   Differences from the source:
--   - encoding: C_P(μ) ≤ 1/ρ and C_LS(μ) ≤ 1/ρ (least constants) → μ satisfies (2) and (3) with constant 1/ρ; reason: the valid constants form a closed up-set, so the least one is ≤ 1/ρ exactly when 1/ρ is valid
--   - reading: μ(dx) = e^{−W(x)}dx → μ a probability measure with this density; reason: Definitions 2–3 are about probability measures, and the measure it is applied to (the posterior of Lemma 6.1) is one; the Φ-entropy is not homogeneous in the mass
--   - reading: ∇²W ⪰ ρ I_n → W twice Fréchet differentiable with D²W(x)(v,v) ≥ ρ‖v‖²; reason: the Hessian condition presupposes that the Hessian exists
--   - encoding: Φ : J → ℝ (every Φ as in Theorem 3.1) → Φ : ℝ → ℝ with AdmissiblePhi J Φ; reason: Lean functions are total; only the values on J (and derivatives at points of the open J) enter
--   - encoding: ℝⁿ → EuclideanSpace ℝ (Fin n); reason: Lean's Euclidean space; same norm, Lebesgue measure and gradient
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Fact A.22, p.62 (PDF 62)

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_PhiSobolev
import Definitions.Def_PhiSobBayes_Poincare
import Definitions.Def_PhiSobBayes_LogSobolev
import Definitions.Def_PhiSobBayes_IsStronglyLogConcave

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Fact A.22 (Bakry–Émery).** Let `μ(dx) = e^{−W(x)} dx` with `∇²W ⪰ ρ I_n` for some `ρ > 0`.
Then `C_P(μ) ≤ 1/ρ` and `C_LS(μ) ≤ 1/ρ`, and more generally `μ` satisfies the Φ-Sobolev inequality (1)
with constant `1/ρ` for every `Φ` as in Theorem 3.1.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Fact A.22, p.62 (PDF 62), citing [BÉ85] and [Cha04, Corollary 2.1].

**Formalization Note** "`C_P(μ) ≤ 1/ρ`" is "`μ` satisfies (2) with constant `1/ρ`", and likewise
for `C_LS` and (3): the least constant is `≤ 1/ρ` exactly when `1/ρ` is a valid constant. "Every `Φ`
as in Theorem 3.1" is every open interval `J` and every `Φ` admissible on `J`. `μ` is a probability
measure (bundled in `IsStronglyLogConcave`). -/
theorem fact_A_22 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (ρ : ℝ) (hρ : 0 < ρ)
    (hμ : IsStronglyLogConcave μ ρ) :
    Poincare μ (1 / ρ) ∧ LogSobolev μ (1 / ρ) ∧
      ∀ (J : Set ℝ) (Φ : ℝ → ℝ), IsOpenInterval J → AdmissiblePhi J Φ →
        PhiSobolev μ J Φ (1 / ρ) := by sorry

end PhiSobBayes
