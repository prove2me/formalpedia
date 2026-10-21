-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_four_query_qubit_transposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.four_query_qubit_transposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:35:22.914409+00:00
-- url     : https://prove2.me/theorems/cbbc9461-84b4-44a6-866d-680719e13e3b
-- title:
--   §7.4, unnumbered main result: exact deterministic qubit-unitary transposition with four uses
-- statement:
--   There exists a deterministic sequential protocol with finite memory and four slots for the same unknown qubit unitary, whose interleaved CPTP maps are all fixed independently of that unitary, such that
--   $$
--   \forall U\in U(2),\qquad \mathcal P[\mathcal U,\mathcal U,\mathcal U,\mathcal U](\rho)
--   =U^{T}\rho\overline U,
--   \quad \mathcal U(\rho)=U\rho U^\dagger.
--   $$
--   The equality is an equality of channels on all operators, including their linear extensions to entangled inputs. The protocol has no postselection and receives no controlled-$U$ oracle. This states exact existence, with no minimality or circuit-size claim.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 44, §7.4, unnumbered main result: exact deterministic qubit-unitary transposition with four uses

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.44, §7.4 main exact-existence claim. Equality is of channels, so
irrelevant global phases are removed. This does not assert minimality or provide
an exact witness from the rounded numerical evidence in Table 2. -/
theorem four_query_qubit_transposition :
    ∃ P : FourUseProtocol, ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      P.run U = conjSuperop (Matrix.transpose (U : Matrix (Fin 2) (Fin 2) ℂ)) := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
