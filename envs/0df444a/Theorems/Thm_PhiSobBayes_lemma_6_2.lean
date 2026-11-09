-- Prove2me | Theorems.Thm_PhiSobBayes_lemma_6_2
-- name    : PhiSobBayes.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:32.772491+00:00
-- url     : https://prove2.me/theorems/b377fc07-2b0d-4ffd-b7dd-930e9cf55b5e
-- title:
--   Lemma 6.2 — the posterior mean attains $R_\Phi(t,f)=\mathbb E_{y}\mathrm{Ent}^\Phi_{\mu_{t,y}}(f)=\mathrm{Ent}^\Phi_\mu(f)-\mathrm{Ent}^\Phi_{\mu K_t}(m)$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^n$, $J$ an open interval, $\Phi:J\to\mathbb R$ smooth and convex, $f$ a $J$-valued function and $t>0$. Let $m(y)=\mathbb E_{\mu_{t,y}}f$ be the posterior mean. Then:
--
--   1. $m$ is a measurable $J$-valued estimator that attains the infimum in $R_\Phi(t,f)=\inf_h\mathbb E B_\Phi(f(X),h(Y_t))$, i.e. $R_\Phi(t,f)=\mathbb E\,B_\Phi(f(X),m(Y_t))$;
--   2. $R_\Phi(t,f)=\mathbb E_{y\sim Y_t}\mathrm{Ent}^\Phi_{\mu_{t,y}}(f)$;
--   3. $\mathbb E_{y\sim Y_t}\mathrm{Ent}^\Phi_{\mu_{t,y}}(f)=\mathrm{Ent}^\Phi_\mu(f)-\mathrm{Ent}^\Phi_{\mu K_t}(m)$;
--   4. in particular, for $\Phi(z)=z^2$ on $J=\mathbb R$, $\mathrm{MMSE}_t(f)=\mathbb E\,\mathrm{Var}(f(X)\mid Y_t)$.
--
--   Together, items 2 and 3 are display (47):
--   $$R_\Phi(t,f)=\mathbb E_{y\sim Y_t}\mathrm{Ent}^\Phi_{\mu_{t,y}}(f)=\mathrm{Ent}^\Phi_\mu(f)-\mathrm{Ent}^\Phi_{\mu K_t}(m).$$
--   This is display (48) in the proof of the goal theorem; both directions start from it.
--
--   Differences from the source:
--   - encoding: f a J-valued function → f J-valued, with f and Φ∘f μ-integrable; reason: without these, f(X) is not a random variable and Ent^Φ_μ(f) and the posterior means are undefined; these are Lemma A.19's hypotheses
--   - encoding: the posterior mean attains the infimum → m is measurable, J-valued, and R_Φ(t, f) equals its risk; reason: an estimator attains the infimum when it is admissible and its risk equals the infimum
--   - encoding: R_Φ(t, f) = 𝔼_y Ent^Φ_{μ_{t,y}}(f) as real numbers → bayesRisk (in [0, ∞]) equals ENNReal.ofReal of the real average; reason: the risk is defined in [0, ∞]; the average of nonnegative entropies is a finite real number
--   - encoding: MMSE_t(f) = 𝔼 Var(f(X) | Y_t) → bayesRisk with J = ℝ and Φ(z) = z² equals ofReal of the average posterior variance, assuming f² μ-integrable; reason: MMSE_t is R_Φ for Φ(z) = z² ((9), p.15), since B_Φ(z, a) = (z − a)²; f² integrable is Φ∘f integrable for this Φ
--   - encoding: μ_{t,y} = L(X | Y_t = y), computed by Bayes' formula (44) → the explicit formula (44) for every y; reason: the paper's own formula; Mathlib's conditional law is only defined almost everywhere
--   - encoding: Φ : J → ℝ smooth and convex → Φ : ℝ → ℝ with ContDiffOn ℝ ∞ Φ J and ConvexOn ℝ J Φ; reason: Lean functions are total; only the values on J (and derivatives at points of the open J) enter
--   - encoding: ℝⁿ → EuclideanSpace ℝ (Fin n); reason: Lean's Euclidean space; same norm, Lebesgue measure and gradient
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma 6.2, p.29 (PDF 29), display (47)

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_phiEnt
import Definitions.Def_PhiSobBayes_bregman
import Definitions.Def_PhiSobBayes_gamJoint
import Definitions.Def_PhiSobBayes_gamObs
import Definitions.Def_PhiSobBayes_posterior
import Definitions.Def_PhiSobBayes_bayesRisk

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Lemma 6.2 (Bayes risk decomposition).** Let `μ` be a probability measure on `ℝⁿ`, `J` an
open interval, `Φ` smooth and convex on `J`, `f` a `J`-valued function and `t > 0`. Then the
posterior mean `m(y) = 𝔼_{μ_{t,y}} f` is a measurable `J`-valued estimator attaining the infimum in
`R_Φ(t, f)`, and `R_Φ(t, f) = 𝔼_{y∼Y_t} Ent^Φ_{μ_{t,y}}(f) = Ent^Φ_μ(f) − Ent^Φ_{μK_t}(m)` (47). In
particular, for `Φ(z) = z²` on `J = ℝ`, `MMSE_t(f) = 𝔼 Var(f(X) | Y_t)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma 6.2, p.29 (PDF 29), display (47).

**Formalization Note** `f` and `Φ ∘ f` are `μ`-integrable (in particular `f` is `μ`-a.e. strongly
measurable): otherwise `Ent^Φ_μ(f)` and the posterior means are undefined. The last clause is the case `J = ℝ`,
`Φ(z) = z²`, where `R_Φ` is `MMSE_t` ((9), p.15) and `Var(f(X) | Y_t = y)` is the variance under the
posterior. -/
theorem lemma_6_2 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (J : Set ℝ) (hJ : IsOpenInterval J) (Φ : ℝ → ℝ) (hΦs : ContDiffOn ℝ ∞ Φ J)
    (hΦc : ConvexOn ℝ J Φ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfJ : ∀ x, f x ∈ J)
    (hf : Integrable f μ) (hΦf : Integrable (fun x => Φ (f x)) μ) (t : ℝ) (ht : 0 < t) :
    let m : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ∫ x, f x ∂(posterior μ t y)
    (Measurable m ∧ (∀ y, m y ∈ J) ∧
      bayesRisk μ J Φ t f = ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (m p.2)) ∂(gamJoint μ t)) ∧
    bayesRisk μ J Φ t f = ENNReal.ofReal (∫ y, phiEnt (posterior μ t y) Φ f ∂(gamObs μ t)) ∧
    ∫ y, phiEnt (posterior μ t y) Φ f ∂(gamObs μ t) = phiEnt μ Φ f - phiEnt (gamObs μ t) Φ m ∧
    (Integrable (fun x => f x ^ 2) μ →
      bayesRisk μ Set.univ (fun z => z ^ 2) t f =
        ENNReal.ofReal (∫ y, variance f (posterior μ t y) ∂(gamObs μ t))) := by sorry

end PhiSobBayes
