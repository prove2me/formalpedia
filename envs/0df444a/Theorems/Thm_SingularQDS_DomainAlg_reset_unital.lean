-- Prove2me | Theorems.Thm_SingularQDS_DomainAlg_reset_unital
-- name    : SingularQDS.DomainAlg.reset_unital
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:38.240572+00:00
-- url     : https://prove2.me/theorems/96ccc554-7019-4e72-a64a-5ee1e8fcecaf
-- title:
--   p. 4 — for every density operator Ω the dual T_t = (S_t)* of the minimal rank-one reset of the left shift is unital
-- statement:
--   Let $\mathcal H = L^2(\mathbb R_+)$, let $W_t\varphi(x) = \varphi(x+t)$ be the semigroup of left shifts, and let $S^0_t[\omega] = W_t\,\omega\,W_t^*$ on trace-class operators with dual $T^0_t[X] = W_t^* X W_t$. Let $\mathcal K_0$ be the generator of $S^0_t$ and fix an arbitrary density operator $\Omega$. The rank-one perturbation
--
--   $$\Lambda[\omega] = -\,\Omega\,\operatorname{Tr}\mathcal K_0[\omega], \qquad \omega \in \operatorname{dom}\mathcal K_0,$$
--
--   re-injects in the state $\Omega$ the probability that the shift moves out through the boundary point $0$. Let $S_t$ be the minimal dynamical semigroup obtained from $\mathcal K_0$ and $\Lambda$ by the resolvent-series construction, and $T_t = (S_t)^*$ its dual. Then $T_t$ is unital:
--
--   $$T_t[I] = I \qquad \text{for all } t \ge 0 .$$
--
--   Equivalently, $S_t$ is trace preserving. In the proof of Lemma 4 this is used in the form $I \in \operatorname{dom}\mathcal L$, $\mathcal L[I] = 0$.
--
--   **Formalization Note** The setting is the published `IsResetConstruction` over the published left-shift pair (`IsLeftShift`, `IsShiftPair`): the perturbation agrees with $-\Omega \operatorname{Tr}\eta$ on the generator graph of $S^0_t$, $S_t$ is the minimal perturbation characterized by its Laplace resolvents, and $T_t$ is the predual partner of $S_t$. The statement is universal: every such construction is unital, for every density operator $\Omega$. Unitality is the published `IsUnitalQDS`.
-- source:
--   Holevo, On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, p. 4 (§2, after (7)); used p. 5, proof of Lemma 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06
open QAlgorithms.Papers.Independent.Renew46.P06
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass State NuclearRepresentation traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators IsUnitalQDS IsRelaxingEvolution)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain DomainPerturbation IsMinimalPerturbation)

namespace SingularQDS.DomainAlg

/-- arXiv:1706.04866v5, p. 4: for every density operator Ω, the dual T_t = (S_t)* of the
minimal rank-one reset perturbation of the left shift is unital. -/
theorem reset_unital (b : HilbertBasis ℕ ℂ HalfLine) (Omega : State b)
    (W : ContractionSemigroup HalfLine) (hShift : IsLeftShift W)
    (Szero : TraceEvolution b) (Tzero : Evolution) (hPair : IsShiftPair b W Szero Tzero)
    (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution)
    (hReset : IsResetConstruction b Szero Omega P S T) :
    IsUnitalQDS T := by sorry

end SingularQDS.DomainAlg
