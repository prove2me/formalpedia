-- Prove2me | Theorems.Thm_WassersteinDRO_Guarantees_finite_sample_guarantees_ii
-- name    : WassersteinDRO.Guarantees.finite_sample_guarantees_ii
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T02:36:03.455651+00:00
-- url     : https://prove2.me/theorems/b78d00f8-cae6-42bd-a235-7df072a7e243
-- title:
--   Theorem 22(a) — Finite sample guarantees II
-- statement:
--   Assume all conditions of Theorem 21 hold and $\varepsilon_N(\eta)$ is as in eq. (28). Then for
--   all $\eta\in(0,1)$ and $\varepsilon\ge\varepsilon_N(\eta)$, $P^N\{R(P,\ell) \le
--   R_\varepsilon(\hat\mu,\hat\Sigma,\ell) \; \forall \ell\in L\} \ge 1-\eta$: with high
--   probability over the training sample, the Gelbrich risk uniformly upper-bounds the true risk
--   across every admissible loss function. (Part (b) of Theorem 22, the analogous bound for the
--   Gelbrich-risk optimization problem's own optimizer, is not formalized in this chunk.)
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Theorem 22, p. 23-24, eq. (29a)

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_empiricalDistribution
import Definitions.Def_WassersteinDRO_Guarantees_nominalRisk
import Definitions.Def_WassersteinDRO_Guarantees_gelbrichRisk
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- Theorem 22 (Finite sample guarantees II), Kuhn et al. 2019, p. 23–24 — the goal theorem,
part (a) (eq. 29a) only; part (b) (eq. 29b), the bound for the Gelbrich-risk-optimization
problem's own optimizer `ℓ*`, is not formalized in this chunk (it needs "`ℓ*` is an optimizer
of the Gelbrich risk optimization problem (19)" as a further object — see `STATUS.md`).
"Assume all conditions of Theorem 21 hold" is spelled out as the same `(µ,Σ,α,A,c)` setup and
`P`/light-tail hypotheses Theorem 21 (`concentration_inequalities_ii`) uses; `ε_N(η) =
log(c/η)/√N` as in eq. (28). Then for all `η ∈ (0,1)` and `ε ≥ ε_N(η)` we have
`P^N{ R(P,ℓ) ≤ R_ε(µ̂,Σ̂,ℓ) ∀ℓ∈L } ≥ 1-η`.
`hΞ : P Ξᶜ = 0` states `Ξ` contains the support of `P`, the paper's own standing assumption
(p. 6: "we let `Ξ ⊆ ℝ^m` be a closed set that is known to contain the support of `P`") that
every later use of `Ξ` (including `Gε(µ̂,Σ̂)` and hence `Rε(µ̂,Σ̂,ℓ)`) presupposes; without it
`Ξ = ∅` is a legal instantiation that makes `gelbrichRisk`'s hull empty and the theorem false.
`hLInt : ∀ ℓ ∈ L, Integrable ℓ P` guards `nominalRisk P ℓ`'s Bochner integral against `L`'s
otherwise-unconstrained loss functions, matching the `Integrable ℓ Q` guard already used
elsewhere in this book wherever `nominalRisk`/`gelbrichRisk` are applied outside the empirical
(automatically-integrable) case, and matching the paper's own Assumption 1 (p. 9). -/
theorem finite_sample_guarantees_ii {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ) (α A c : ℝ)
    (hα : 2 < α) (hA : 0 < A) (hc : c > 1)
    (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ)
    (hP : IsProbabilityMeasure P) (hN : 0 < N)
    (hμ : meanVector P = μ) (hSigma : covarianceMatrix P = Sigma)
    (hInt : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (hA' : (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A)
    (Ξ : Set (EuclideanSpace ℝ (Fin m))) (hΞ : P Ξᶜ = 0)
    (L : Set (EuclideanSpace ℝ (Fin m) → ℝ)) (hLInt : ∀ ℓ ∈ L, Integrable ℓ P)
    (η ε : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hε : ε ≥ Real.log (c / η) / Real.sqrt N) :
    sampleMeasure P N
        {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
          ∀ ℓ ∈ L, (nominalRisk P ℓ : EReal) ≤
            gelbrichRisk ε Ξ (meanVector (empiricalDistribution ξhat))
              (covarianceMatrix (empiricalDistribution ξhat)) ℓ} ≥
      ENNReal.ofReal (1 - η) := by sorry

end WassersteinDRO.Guarantees
