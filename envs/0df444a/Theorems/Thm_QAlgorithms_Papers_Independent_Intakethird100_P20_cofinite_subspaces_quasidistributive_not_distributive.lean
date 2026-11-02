-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_cofinite_subspaces_quasidistributive_not_distributive
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.cofinite_subspaces_quasidistributive_not_distributive
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:37:04.39231+00:00
-- url     : https://prove2.me/theorems/335f8fe3-b39e-4c5c-b35e-ed126a6e8bc3
-- title:
--   example-3.2
-- statement:
--   For an infinite-dimensional complex Hilbert space, let $L_{\mathrm{cof}}(H)$ consist of zero and all closed subspaces of finite codimension. It is closed under the inherited binary meet and join, is not distributive, and has exactly one quasipoint:
--
--   $$Q(L_{\mathrm{cof}}(H))=\{L_{\mathrm{cof}}(H)\setminus\{0\}\}.$$
--
--   Consequently the basic sets satisfy the quasidistributive identity $Q_{(U\wedge V)\vee(U\wedge W)}=Q_{U\wedge(V\vee W)}$. This is the concrete counterexample separating quasidistributivity from distributivity.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 43, example-3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- example-3.2; de Groote, Observables I, PDF p./pp. 43.
-/
theorem cofinite_subspaces_quasidistributive_not_distributive {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinfinite : ¬ FiniteDimensional ℂ H) :
    (∀ U V : CofiniteSubspaces H,
      ((U.val ⊓ V.val = ⊥ ∨ FiniteDimensional ℂ (U.val ⊓ V.val).orthogonal.toSubmodule) ∧
       (U.val ⊔ V.val = ⊥ ∨ FiniteDimensional ℂ (U.val ⊔ V.val).orthogonal.toSubmodule))) ∧
    (∃ U V W : CofiniteSubspaces H,
      U.val ⊓ (V.val ⊔ W.val) ≠ (U.val ⊓ V.val) ⊔ (U.val ⊓ W.val)) ∧
    IsQuasipoint {U : CofiniteSubspaces H | U.val ≠ ⊥} ∧
    (∀ B : StoneSpectrum (CofiniteSubspaces H), B.val = {U | U.val ≠ ⊥}) ∧
    (∀ U V W : CofiniteSubspaces H,
      cofiniteBasic ((U.val ⊓ V.val) ⊔ (U.val ⊓ W.val)) =
        cofiniteBasic (U.val ⊓ (V.val ⊔ W.val))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
