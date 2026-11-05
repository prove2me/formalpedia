-- Prove2me | Theorems.Thm_RepGQML_commutant_block_diagonal
-- name    : RepGQML.commutant_block_diagonal
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:37.190976+00:00
-- url     : https://prove2.me/theorems/043dc715-beb1-4237-b7a8-87cd2d21b685
-- title:
--   (31)–(32) — elements of the commutant are block diagonal across irreps
-- statement:
--   Let $\Phi$ be a decomposition $U=\bigoplus_k\mathbb 1_{m_k}\otimes\rho_k$ into irreps, and let $T\in\mathcal C(U)$. If $x\in H$ has $\Phi(x)_j=0$ for all $j\ne l$, then
--   $$
--   \Phi(Tx)_k=0\qquad\text{for all } k\ne l .
--   $$
--   So in the identification $\Phi$, the off-diagonal blocks of $T$ vanish. This is the zero pattern in the display (32) of the source, matching the block form (31) of $U$.
--
--   Differences from the source:
--   - reading: the matrix display (32), with zeros outside the diagonal blocks → vectors supported on summand l are sent to vectors supported on summand l; reason: this is the meaning of the zero entries of the display; the blocks themselves are the subject of the goal
--   - reading: the irreps U_k of Theorem 7, not said to be inequivalent → pairwise inequivalent, through IsIrrepDecomposition; reason: multiplicities are defined by that reading (p.21, p.30, footnote 20); without it (30) is false, as in the goal
--   - generalization: a unitary representation of a compact group, with the source's block identification → any group, any representation U on a complex space, Φ only linear; reason: compactness and unitarity of U play no part; the isometric case is included
--   - encoding: U = ⨁ 𝟙 ⊗ U_k, an equality after a change of basis → the identification Φ; reason: Lean needs the identification explicit; same decompositions
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, p.28, the sentence leading into (31)–(32), and (32), p.29

import Mathlib
import Definitions.Def_RepGQML_commutant
import Definitions.Def_RepGQML_groupAlgebra
import Definitions.Def_RepGQML_IsIrrepDecomposition

namespace RepGQML

/-- The elements of the commutant are block diagonal across `k` (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, p.28 and display (32), p.29):
under a decomposition `Φ`, an operator `T` commuting with `U` sends a vector supported on the `l`-th
summand to a vector supported on the `l`-th summand. -/
theorem commutant_block_diagonal {G H K : Type*} [Group G] [AddCommGroup H] [Module ℂ H] [Fintype K]
    {U : Representation ℂ G H} {m : K → ℕ} {V : K → Type*} [∀ k, NormedAddCommGroup (V k)]
    [∀ k, InnerProductSpace ℂ (V k)] {ρ : ∀ k, Representation ℂ G (V k)}
    {Φ : H ≃ₗ[ℂ] IrrepSum m V} (hΦ : IsIrrepDecomposition U m V ρ Φ)
    (T : Module.End ℂ H) (hT : T ∈ commutant (groupAlgebra U)) (l : K) (x : H)
    (hx : ∀ j, j ≠ l → Φ x j = 0) (k : K) (hk : k ≠ l) :
    Φ (T x) k = 0 := by sorry

end RepGQML
