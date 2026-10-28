-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P30_relative_entanglement_nonlocking
-- name    : QAlgorithms.Papers.Independent.Frontier30.P30.relative_entanglement_nonlocking
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:32:06.407227+00:00
-- url     : https://prove2.me/theorems/a8e73b6f-4800-4bb3-b98d-892063a6f32f
-- title:
--   Relative entropy loses at most one bit under measurement and two under erasure
-- statement:
--   Let $\rho$ be any normalized density matrix across $AA':B$, where $A$ is exactly a qubit and $A',B$ are arbitrary positive finite-dimensional complex systems. Let $\Lambda_A$ be any complete rank-one projective measurement on $A$, with its outcome forgotten. For relative entropy of entanglement $E_r$ in bits, minimized over separable normalized densities on the displayed cut,
--
--   $$E_r(\rho)-E_r((\Lambda_A\otimes I_{A'B})(\rho))\le1,\qquad E_r(\rho)-E_r(\operatorname{Tr}_A\rho)\le2.$$
--
--   The second comparison uses the cut $A':B$. Thus neither operation can lock an unbounded amount of relative entropy of entanglement.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, PDF p. 2, Proposition 1, Eqs. (7)–(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:quant-ph/0404096v1, PDF pp.2--3, Proposition 1, both (7),(8).
The proof's I_A/4 is a typo for I_A/2; the proposition's constants are unchanged. -/
theorem relative_entanglement_nonlocking {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Op ((Fin 2 × A) × B)) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    relativeE rho - relativeE (measureFlag U rho) ≤ 1 ∧
    relativeE rho - relativeE (eraseFlag rho) ≤ 2 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P30

end
