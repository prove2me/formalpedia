-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_diagonal_replacement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.diagonal_replacement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:28:24.455554+00:00
-- url     : https://prove2.me/theorems/6a8520bb-456d-41f7-b19a-056c1672cc04
-- title:
--   Classical dephasing preserves every replicated POVM
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Assume $N\ge1$. Choose any admissible learner $S$ and any causal class allowing an initial group of $k$ source calls in parallel. Let $\Delta$ dephase all original classical outcome wires in their fixed basis. Its actual diagonal slices $S'_{i,j}=\langle j|S_i|j\rangle$ are positive, and
--
--   $$\Delta(S)_i=\sum_j S'_{i,j}\otimes |j\rangle\langle j|,\qquad G^{\Delta(S)}(U)=G^S(U)\quad\text{for every }U\in SU(d).$$
--
--   The replacement is diagonal and obeys the same causal constraints. Tensor factors here mean the fixed target, classical-string, source-input coordinate ordering. This operational replacement preserves more than an averaged objective.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 4, Lemma 2 (Restriction to diagonal network)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF p.4, Lemma 2, (19)-(21): dephasing preserves causal feasibility and
EVERY replica for EVERY U, not merely an average score. -/
theorem diagonal_replacement {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    (k : ℕ) (S : Branches d N) (hS : LearningInstrument k S) :
    LearningInstrument k (outcomeDephasing S) ∧ IsDiagonal (outcomeDephasing S) ∧
    (∀ i j, (outcomeBlocks S i j).PosSemidef) ∧
    (∀ i a b, outcomeDephasing S i a b =
      if a.2.1 = b.2.1 then outcomeBlocks S i a.2.1 (a.1,a.2.2) (b.1,b.2.2) else 0) ∧
    ∀ U : SU d, replicatedPOVM (outcomeDephasing S) (U : (Matrix (Fin d) (Fin d) ℂ)) =
      replicatedPOVM S (U : (Matrix (Fin d) (Fin d) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
