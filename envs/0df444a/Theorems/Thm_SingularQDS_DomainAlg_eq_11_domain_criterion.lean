-- Prove2me | Theorems.Thm_SingularQDS_DomainAlg_eq_11_domain_criterion
-- name    : SingularQDS.DomainAlg.eq_11_domain_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:40.778907+00:00
-- url     : https://prove2.me/theorems/f1eb0c3a-b2e9-4331-b4fa-97956bc4a166
-- title:
--   (11), p. 5 — X is in the domain of the generator iff sup_{t>0} t⁻¹‖T_t[X] − X‖ < ∞
-- statement:
--   Let $\mathcal H = L^2(\mathbb R_+)$ and let $T_t$, $t \ge 0$, be an arbitrary quantum dynamical semigroup on $\mathfrak B(\mathcal H)$: a one-parameter semigroup of normal, completely positive, subunital maps with $T_0 = \mathrm{Id}$ and $t \mapsto T_t[X]$ weakly continuous for every bounded $X$. Its generator $\mathcal L$ is the ultraweak (weak$^*$) generator: $X \in \operatorname{dom}\mathcal L$ with $\mathcal L[X] = Y$ means that for every trace-class operator $\rho$,
--
--   $$\lim_{t \downarrow 0} t^{-1}\bigl(\operatorname{Tr}\rho\, T_t[X] - \operatorname{Tr}\rho X\bigr) = \operatorname{Tr}\rho\, Y .$$
--
--   Arveson's criterion states that a bounded operator $X$ lies in $\operatorname{dom}\mathcal L$ if and only if the difference quotients are bounded in operator norm:
--
--   $$X \in \operatorname{dom}\mathcal L \iff \sup_{t>0} t^{-1}\,\|T_t[X] - X\| \le M < \infty \ \text{ for some } M .$$
--
--   This is criterion (iii) of Lemma 1 in Arveson's paper, used in the proofs of Lemmas 3 and 4 to move between estimates of difference quotients and membership in the generator domains of the shift semigroup and of its perturbation.
--
--   **Formalization Note** The semigroup is the published `Evolution` on $L^2(\mathbb R_+)$, and the generator domain is the published ultraweak domain `dualGeneratorDomain` (tested by every trace-class $\rho$), not an operator-norm derivative, for which the criterion would be false. The statement is on $L^2(\mathbb R_+)$ only because that domain is defined there; nothing in it uses the shift. The norm is the operator norm, and real times $t > 0$ enter the semigroup through `t.toNNReal`.
-- source:
--   Holevo, On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, p. 5, (11)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06
open QAlgorithms.Papers.Independent.Renew46.P06
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass State NuclearRepresentation traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators IsUnitalQDS IsRelaxingEvolution)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain DomainPerturbation IsMinimalPerturbation)

namespace SingularQDS.DomainAlg

/-- arXiv:1706.04866v5, p. 5, (11): for an arbitrary quantum dynamical semigroup on
B(L²(ℝ₊)), X lies in the domain of the ultraweak generator iff t⁻¹‖T_t[X] − X‖ is bounded
over t > 0 (operator norm). -/
theorem eq_11_domain_criterion (b : HilbertBasis ℕ ℂ HalfLine) (T : Evolution)
    (X : HalfLine →L[ℂ] HalfLine) :
    X ∈ dualGeneratorDomain b T ↔
      ∃ M : ℝ, ∀ t : ℝ, 0 < t → t⁻¹ * ‖T.maps t.toNNReal X - X‖ ≤ M := by sorry

end SingularQDS.DomainAlg
