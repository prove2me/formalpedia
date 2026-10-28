-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_boundedRankKraus_schmidt_outputs_and_peb
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.boundedRankKraus_schmidt_outputs_and_peb
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:04:58.307067+00:00
-- url     : https://prove2.me/theorems/b0dabfec-0337-4274-89db-f026abe61313
-- title:
--   Bounded-rank Kraus operators give Schmidt-rank-r outputs and r-partial entanglement breaking
-- statement:
--   Let $\Psi$ be a channel with a countable Kraus representation whose operators have rank at most $r\ge 1$. Then for every ancilla every output $(\Psi\otimes\mathrm{Id})(\omega)$ is a countable convex combination of pure states of Schmidt rank at most $r$, and $\Psi$ is $r$-partially entanglement breaking:
--
--   $$\operatorname{rank}V_k\le r\ \ \forall k\ \Longrightarrow\ \Psi\ \text{has countable Schmidt-rank-}r\text{ outputs and is } r\text{-PEB}.$$
--
--   Role: turns the Kraus clause of Theorem 3 into its two entanglement clauses.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, Theorem 3 and the remarks after it (PDF pp. 7-9: a channel with Kraus operators of rank <= r is r-partially entanglement breaking); M. Horodecki, P. W. Shor, M. B. Ruskai, Rev. Math. Phys. 15 (2003) 629-641 (Kraus rank-one characterisation of entanglement breaking, generalised to rank r by D. Chruscinski and A. Kossakowski, Open Sys. Inf. Dyn. 13 (2006) 17-26)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

theorem boundedRankKraus_schmidt_outputs_and_peb {I E : Type} [Countable I] [Countable E] [Nonempty I] [Nonempty E]
    (Psi : Channel I E) (r : ℕ) (bound : ℕ∞) (hr : 0 < r)
    (hK : HasBoundedRankKraus Psi.val r bound) :
    CountableSchmidtOutputs Psi.val r ∧ PartiallyEntanglementBreaking Psi.val r := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
