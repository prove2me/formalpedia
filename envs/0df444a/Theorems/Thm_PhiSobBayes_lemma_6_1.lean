-- Prove2me | Theorems.Thm_PhiSobBayes_lemma_6_1
-- name    : PhiSobBayes.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:18.369034+00:00
-- url     : https://prove2.me/theorems/a9347cad-1b48-45b5-aff5-fea0918ac9e1
-- title:
--   Lemma 6.1 — posteriors of a log-concave prior are $t$-strongly log-concave
-- statement:
--   If $\mu$ is a log-concave probability measure on $\mathbb R^n$, then for every $t>0$ and every $y\in\mathbb R^n$ the posterior $\mu_{t,y}$ is $t$-strongly log-concave: $\mu_{t,y}(dx)=e^{-W(x)}\,dx$ with $\nabla^2W\succeq t\,I_n$.
--
--   Combined with the Bakry–Émery criterion, it gives every posterior the $\Phi$-Sobolev inequality with constant $1/t$, which is the first step of (49).
--
--   Differences from the source:
--   - reading: μ(dx) = e^{−V(x)}dx with ∇²V ⪰ 0 (and W with ∇²W ⪰ t I_n) → V and W twice Fréchet differentiable with D²V(x)(v,v) ≥ 0 and D²W(x)(v,v) ≥ t‖v‖²; reason: the Hessian condition presupposes that the Hessian exists; no stronger regularity is asked
--   - encoding: μ_{t,y} = L(X | Y_t = y), computed by Bayes' formula (44) → the explicit formula (44) for every y; reason: the paper's own formula; Mathlib's conditional law is only defined almost everywhere
--   - encoding: ℝⁿ → EuclideanSpace ℝ (Fin n); reason: Lean's Euclidean space; same norm, Lebesgue measure and gradient
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma 6.1, p.29 (PDF 29)

import Mathlib
import Definitions.Def_PhiSobBayes_IsLogConcave
import Definitions.Def_PhiSobBayes_IsStronglyLogConcave
import Definitions.Def_PhiSobBayes_posterior

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Lemma 6.1 (posterior log-concavity).** If `μ` is log-concave, then for every `t > 0` and
`y ∈ ℝⁿ` the posterior `μ_{t,y}` is `t`-strongly log-concave: `μ_{t,y}(dx) = e^{−W(x)} dx` with
`∇²W ⪰ t I_n`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma 6.1, p.29 (PDF 29). -/
theorem lemma_6_1 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : IsLogConcave μ) (t : ℝ) (ht : 0 < t)
    (y : EuclideanSpace ℝ (Fin n)) : IsStronglyLogConcave (posterior μ t y) t := by sorry

end PhiSobBayes
