-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_separable_decomposition_length
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.separable_decomposition_length
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:47.019597+00:00
-- url     : https://prove2.me/theorems/15d71ec7-9b4c-4aa6-90cd-14c55fb40b36
-- title:
--   Lemma 8: product decomposition length at most the common global/marginal rank
-- statement:
--   Let $\rho$ be a separable density matrix on $\mathbb C^a\otimes\mathbb C^b$, with $a,b\ge1$. Suppose both $\rho$ and its first marginal $\rho_A=\operatorname{Tr}_B\rho$ have rank $r$. Then there exist $m\le r$, nonnegative weights $p_k$ summing to one, and unit vectors $u_k\in\mathbb C^a$, $v_k\in\mathbb C^b$ such that
--
--   $$\rho=\sum_{k=1}^{m}p_k|u_k\rangle\langle u_k|\otimes|v_k\rangle\langle v_k|.$$
--
--   The rank $r$ is independent of the ambient dimensions. First proved in [10], the lemma receives a new proof here and bounds the length of separable decompositions under a matching marginal-rank assumption.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Lemma 8: product decomposition length at most the common global/marginal rank, PDF p. 10. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02
































































/-- Lemma 8, PDF p.10, proof pp.10–11, introduced p.9.
The common rank r is separate from both ambient dimensions.
First proved in [10]; this paper gives a new proof. -/
theorem separable_decomposition_length (a b r : ℕ) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hDensity : IsDensityMatrix rho)
    (hSeparable : letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
      letI : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
      Entanglement.IsSeparableDensity rho)
    (hRank : rho.rank = r) (hMarginal : (traceRight rho).rank = r) :
    ∃ m : ℕ, m ≤ r ∧ ∃ weights : Fin m → ℝ,
      (∀ k, 0 ≤ weights k) ∧ (∑ k, weights k) = 1 ∧
      ∃ u : Fin m → StateVector a, ∃ v : Fin m → StateVector b,
        (∀ k, IsState (u k) ∧ IsState (v k)) ∧
        rho = ∑ k, (weights k : ℂ) • Matrix.kronecker (pureDensity (u k)) (pureDensity (v k)) := by sorry





end QAlgorithms.Papers.Independent.Independent1.P02
