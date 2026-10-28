-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_zero_entanglement
-- name    : QAlgorithms.Papers.Independent.Support50.P42.zero_entanglement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:24:45.886306+00:00
-- url     : https://prove2.me/theorems/74bba14d-1049-4c9d-9c80-f81a1689683f
-- title:
--   No positive-probability entangled pure output from a product input
-- statement:
--   Let the shared input be a normalized pure state with entropy of entanglement zero. Consider any finite adaptive local protocol, allowing classical messages, local ancillas, disposal and postselection. Every pure final leaf of positive probability satisfies
--
--   $$p_j>0\quad\Longrightarrow\quad E(\psi_j)=0.$$
--
--   Consequently an entangled pure target cannot be prepared with any positive success probability. This retains the source's exact postselection obstruction, rather than only a zero asymptotic rate; formal zero-probability leaves do not count as successful preparations.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 16, §V: no positive-probability creation from a product input

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.16: exact postselection obstruction; every positive-probability pure
leaf from a product input has zero entanglement. Zero-downCount leaves do not
witness successful preparation. -/
theorem zero_entanglement (s : Shared) (hs : IsPureShared s) (hzero : ent s=0)
    (out : List (ℝ × Shared)) (hlocal : LocalTree s out) :
    ∀ w∈out, 0<w.1 → IsPureShared w.2 → ent w.2=0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
