-- Prove2me | Theorems.Thm_SingularQDS_DomainAlg_variance_vanishes
-- name    : SingularQDS.DomainAlg.variance_vanishes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:20.587301+00:00
-- url     : https://prove2.me/theorems/6e7dc2fa-9c7e-401d-ba5a-3cf9d1158b14
-- title:
--   Proof of Theorem 2, p. 6 — for X in the domain algebra, Tr ΩX*X = |Tr ΩX|² and Tr ΩXX* = |Tr ΩX*|²
-- statement:
--   In the setting of the rank-one reset of the left shift on $\mathcal H = L^2(\mathbb R_+)$ (an arbitrary density operator $\Omega$, the shift semigroup $T^0_t$, the minimal perturbed semigroup $T_t$ with ultraweak generator $\mathcal L$), let
--
--   $$\mathcal A = \{X \in \operatorname{dom}\mathcal L : X^*X \in \operatorname{dom}\mathcal L,\ XX^* \in \operatorname{dom}\mathcal L\}$$
--
--   be Arveson's domain algebra. For every $X \in \mathcal A$,
--
--   $$\operatorname{Tr}\Omega X^*X = |\operatorname{Tr}\Omega X|^2 \qquad\text{and}\qquad \operatorname{Tr}\Omega XX^* = |\operatorname{Tr}\Omega X^*|^2 .$$
--
--   The first identity is the step "this is possible iff $\operatorname{Tr}\Omega X^*X = |\operatorname{Tr}\Omega X|^2$" of the proof of Theorem 2; the second is the same step applied to $XX^*$, with $X^*$ in the role of $X$. Combined with the equality case of the noncommutative Cauchy–Schwarz inequality, they give $[X - (\operatorname{Tr}\Omega X)I]\Omega = \Omega[X - (\operatorname{Tr}\Omega X)I] = 0$.
--
--   **Formalization Note** The setting is the published `IsResetConstruction` over the published left-shift pair, exactly the binders of the mission goal; $\mathcal A$ is the published `domainAlgebra`, $\operatorname{Tr}\Omega Y$ the published basis trace of $\Omega Y$, and $|z|^2$ is `Complex.normSq z` cast to $\mathbb C$.
-- source:
--   Holevo, On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, p. 6, proof of Theorem 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06
open QAlgorithms.Papers.Independent.Renew46.P06
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass State NuclearRepresentation traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators IsUnitalQDS IsRelaxingEvolution)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain DomainPerturbation IsMinimalPerturbation)

namespace SingularQDS.DomainAlg

/-- arXiv:1706.04866v5, p. 6, proof of Theorem 2: for X in the domain algebra of the reset
semigroup, Tr ΩX*X = |Tr ΩX|², and (the similar argument applied to XX*)
Tr ΩXX* = |Tr ΩX*|². -/
theorem variance_vanishes (b : HilbertBasis ℕ ℂ HalfLine) (Omega : State b)
    (W : ContractionSemigroup HalfLine) (hShift : IsLeftShift W)
    (Szero : TraceEvolution b) (Tzero : Evolution) (hPair : IsShiftPair b W Szero Tzero)
    (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution)
    (hReset : IsResetConstruction b Szero Omega P S T)
    (X : HalfLine →L[ℂ] HalfLine) (hX : X ∈ domainAlgebra b T) :
    operatorTrace b (Omega.val.val.comp (X.adjoint.comp X)) =
        (Complex.normSq (operatorTrace b (Omega.val.val.comp X)) : ℂ) ∧
      operatorTrace b (Omega.val.val.comp (X.comp X.adjoint)) =
        (Complex.normSq (operatorTrace b (Omega.val.val.comp X.adjoint)) : ℂ) := by sorry

end SingularQDS.DomainAlg
