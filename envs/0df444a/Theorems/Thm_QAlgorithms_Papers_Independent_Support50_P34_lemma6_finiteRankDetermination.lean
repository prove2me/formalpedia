-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_lemma6_finiteRankDetermination
-- name    : QAlgorithms.Papers.Independent.Support50.P34.lemma6_finiteRankDetermination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:43:37.803272+00:00
-- url     : https://prove2.me/theorems/67fabe6b-b1e7-4a27-96ad-0c924d81d9ec
-- title:
--   Lemma 6: determination by finite-rank states
-- statement:
--   Let $f,g:S(\mathcal H)\to[-\infty,+\infty]$ each be concave, lower semicontinuous, and bounded below by a real number. If they agree on the finite-rank states $S_f(\mathcal H)$, then
--
--   $$f|_{S_f(\mathcal H)}=g|_{S_f(\mathcal H)}\quad\Longrightarrow\quad f=g.$$
--
--   Both functions may take the value $+\infty$. This states uniqueness from finite-rank data, rather than mere existence of a restriction.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 14, Lemma 6: determination by finite-rank states

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State PositiveTraceClass traceNormValue stateTraceNormTopology traceNormTopology
   operatorTrace IsPositive IsTraceClass stateEntropy relativeEntropy entropyWeight)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*}

section Statements

variable [hsep : TopologicalSpace.SeparableSpace H] [hI : Countable I]

include hsep hI

/-- Lemma 6, arXiv:0904.1963v3, PDF p.14: uniqueness for two functions,
including infinite values. -/
theorem lemma6_finiteRankDetermination (b : HilbertBasis I ℂ H)
    (f g : QuantumState b → EReal) (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) (hfb : LowerBounded f) (hgb : LowerBounded g)
    (hfc : StateConcaveOn b Set.univ f) (hgc : StateConcaveOn b Set.univ g)
    (hfg : ∀ rho ∈ finiteRankStates b, f rho = g rho) : f = g := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
