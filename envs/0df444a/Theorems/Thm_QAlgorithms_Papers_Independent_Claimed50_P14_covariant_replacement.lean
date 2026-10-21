-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_covariant_replacement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.covariant_replacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:29:14.047373+00:00
-- url     : https://prove2.me/theorems/cd6e4806-3250-40c2-8f1a-01e8de496acd
-- title:
--   Special-unitary twirling gives a covariant replacement
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Assume $N\ge1$ and let $S$ be any admissible diagonal learner. Put $V(U)=\overline U_{\rm target}\otimes U_{\rm input}^{\otimes N}\otimes I_{\rm classical}$, with the factors placed in the fixed coordinate ordering, and define
--
--   $$R_i=\int_{SU(d)} V(U)S_iV(U)^\dagger\,dU.$$
--
--   The integral is integrable without additional assumptions. The learner $R$ is admissible and diagonal, satisfies $[R_i,V(U)]=0$, and $D(R)\le D(S)$. Its own replica satisfies
--
--   $$G_i^R(U)=U G_i^R(I)U^\dagger\qquad\text{for every }U,i.$$
--
--   Thus covariance may be imposed in the optimization; no equality with the original learner's individual replicas is claimed.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 4, Lemma 3 (Covariant networks)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.4-5, Lemma 3: explicit twirling, non-increase of D, and
covariance of the replacement's own replica. Integrability is a conclusion. -/
theorem covariant_replacement {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    (S : Branches d N) (hS : LearningInstrument 0 S) (hdiag : IsDiagonal S) :
    LearningInstrument 0 (covariantTwirl S) ∧ IsDiagonal (covariantTwirl S) ∧
    IsLearningCovariant (covariantTwirl S) ∧
    learningDistance (by omega : 0 < d) (covariantTwirl S) ≤
      learningDistance (by omega : 0 < d) S ∧
    (∀ U : SU d, ∀ i, replicatedPOVM (covariantTwirl S) (U : (Matrix (Fin d) (Fin d) ℂ)) i =
      (U : (Matrix (Fin d) (Fin d) ℂ)) * replicatedPOVM (covariantTwirl S) 1 i * (U : (Matrix (Fin d) (Fin d) ℂ))ᴴ) ∧
    (∀ i, Integrable (fun U : SU d => covariantRepresentation (U : (Matrix (Fin d) (Fin d) ℂ)) *
      S i * (covariantRepresentation (U : (Matrix (Fin d) (Fin d) ℂ)))ᴴ) (specialUnitaryHaar d)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
