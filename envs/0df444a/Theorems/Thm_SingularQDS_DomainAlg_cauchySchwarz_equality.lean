-- Prove2me | Theorems.Thm_SingularQDS_DomainAlg_cauchySchwarz_equality
-- name    : SingularQDS.DomainAlg.cauchySchwarz_equality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:28.76376+00:00
-- url     : https://prove2.me/theorems/6807fb9c-6c49-44e6-b5f4-e48bf82c60fe
-- title:
--   Proof of Theorem 2, p. 6 — Tr ΩX*X ≥ |Tr ΩX|², with equality iff [X − (Tr ΩX)I]Ω = 0
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space, $\Omega$ a density operator on $\mathcal H$ (a positive trace-class operator with $\operatorname{Tr}\Omega = 1$) and $X$ a bounded operator. The noncommutative Cauchy–Schwarz inequality says that $\operatorname{Tr}\Omega X^*X$ is a real number and
--
--   $$\operatorname{Tr}\Omega X^*X \ \ge\ |\operatorname{Tr}\Omega X|^2 ,$$
--
--   and its equality case says that equality holds if and only if
--
--   $$[X - (\operatorname{Tr}\Omega X)\, I]\,\Omega = 0 .$$
--
--   In the proof of Theorem 2 this converts the variance identity $\operatorname{Tr}\Omega X^*X = |\operatorname{Tr}\Omega X|^2$ for $X$ in the domain algebra into the annihilation $[X - (\operatorname{Tr}\Omega X)I]\Omega = 0$.
--
--   **Formalization Note** The statement is on an arbitrary complex Hilbert space with a Hilbert basis indexed by an arbitrary type; $\Omega$ is the published `State` (positive, self-adjoint, nuclear, basis trace one), $\operatorname{Tr}$ the published basis trace, and $|z|^2$ is `Complex.normSq z`. The realness of $\operatorname{Tr}\Omega X^*X$ is stated explicitly (imaginary part zero), and the inequality compares its real part.
-- source:
--   Holevo, On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, p. 6, proof of Theorem 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06
open QAlgorithms.Papers.Independent.Renew46.P06
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass State NuclearRepresentation traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators IsUnitalQDS IsRelaxingEvolution)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain DomainPerturbation IsMinimalPerturbation)

namespace SingularQDS.DomainAlg

/-- arXiv:1706.04866v5, p. 6, proof of Theorem 2: for a density operator Ω on any complex
Hilbert space and a bounded X, Tr ΩX*X is real, Tr ΩX*X ≥ |Tr ΩX|², and equality holds iff
[X − (Tr ΩX) I] Ω = 0. -/
theorem cauchySchwarz_equality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} (b : HilbertBasis ι ℂ H) (Omega : State b)
    (X : H →L[ℂ] H) :
    let c := operatorTrace b (Omega.val.val.comp X)
    let v := operatorTrace b (Omega.val.val.comp (X.adjoint.comp X))
    v.im = 0 ∧ Complex.normSq c ≤ v.re ∧
      (v = (Complex.normSq c : ℂ) ↔
        (X - c • ContinuousLinearMap.id ℂ H).comp Omega.val.val = 0) := by sorry

end SingularQDS.DomainAlg
