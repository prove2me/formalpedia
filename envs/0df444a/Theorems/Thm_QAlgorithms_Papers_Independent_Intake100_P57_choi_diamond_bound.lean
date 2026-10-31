-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P57_choi_diamond_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P57.choi_diamond_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:58:30.986263+00:00
-- url     : https://prove2.me/theorems/6331d688-e720-4af4-8bf0-b3308da92afd
-- title:
--   Diamond distance bounded by normalized Choi distance
-- statement:
--   Let $A,B$ be nonempty finite-dimensional quantum registers with fixed computational bases, and let $\Omega_1,\Omega_2:\mathcal B(A)\to\mathcal B(B)$ be CPTP maps. With a reference register $C$ isomorphic to $A$, let $J(\Omega)=(\Omega\otimes\mathrm{id}_C)(|\Phi_A\rangle\langle\Phi_A|)$ be the normalized Choi state, ordered as output followed by reference. Then
--
--   $$
--   \|\Omega_1-\Omega_2\|_\diamond\le2\dim(A)\,\|J(\Omega_1)-J(\Omega_2)\|_1.
--   $$
--
--   Here $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$ and the diamond norm has no factor $1/2$. This converts normalized Choi-state estimates into worst-case channel estimates.
--
--   **Formalization Note** The accepted Choi state puts reference first; an explicit coordinate swap restores the source's order.
-- source:
--   Simplified instantaneous non-local quantum computation with applications to position-based cryptography, arXiv:1101.1065v3, PDF p. 8, II.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P57

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P57

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- P34 uses half the channel distance. Every occurrence below is multiplied by two.

open QAlgorithms.Papers.Independent.Information100.P34 (diamondDistance)

open QAlgorithms.Papers.Independent.Dependency50.P07 (ensembleMean)

/-- Lemma II.3, PDF p.8 (definition on p.7): normalized Choi bound for two
CPTP maps on arbitrary nonempty finite registers. The printed factor 2 is retained. -/
theorem choi_diamond_bound {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F G : Superop I O) (hF : IsChannel F) (hG : IsChannel G) :
    2 * diamondDistance F G ≤ 2 * (Fintype.card I : ℝ) *
      traceNorm (sourceChoi F - sourceChoi G) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P57

end
