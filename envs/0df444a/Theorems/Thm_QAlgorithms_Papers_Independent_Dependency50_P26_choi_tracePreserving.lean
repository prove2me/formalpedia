-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_choi_tracePreserving
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.choi_tracePreserving
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:25:56.126456+00:00
-- url     : https://prove2.me/theorems/3a608912-89b4-4169-8211-8edba1701044
-- title:
--   Lemma 1: trace preservation
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\mathcal M:L(H_0)\to L(H_1)$ be complex-linear, and let $C(\mathcal M)$ be its output-first unnormalized Choi operator. Trace preservation on every operator is equivalent to
--
--   $$
--   \forall X,\ \operatorname{Tr}\mathcal M(X)=\operatorname{Tr}X\quad\Longleftrightarrow\quad\operatorname{Tr}_{H_1}C(\mathcal M)=I_{H_0}.
--   $$
--
--   Characterizes channel normalization independently of complete positivity.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 2, Lemma 1: trace preservation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.2, Lemma 1. Finite nonempty coordinate types carry the fixed bases. -/
theorem choi_tracePreserving {I O : Type*} [Fintype I] [Fintype O]
    [Nonempty I] [Nonempty O] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    TracePreserving M ↔ traceLeft (outputFirstChoi M) = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
