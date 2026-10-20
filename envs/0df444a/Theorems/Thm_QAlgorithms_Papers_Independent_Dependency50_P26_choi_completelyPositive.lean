-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_choi_completelyPositive
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.choi_completelyPositive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:27:42.890782+00:00
-- url     : https://prove2.me/theorems/d6b80d90-0902-419c-8c87-fd5393e7b737
-- title:
--   Lemma 3: complete positivity
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\mathcal M:L(H_0)\to L(H_1)$ be complex-linear. Complete positivity means positivity after tensoring with the identity on every finite ancilla. Then
--
--   $$
--   \mathcal M\text{ is completely positive}\quad\Longleftrightarrow\quad C(\mathcal M)\succeq0.
--   $$
--
--   This is the Choi characterization; the source attributes the Kraus representation used in its proof to reference [1].
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 3, Lemma 3: complete positivity

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.3, Lemma 3; the Kraus characterization in the proof is attributed there to [1]. -/
theorem choi_completelyPositive {I O : Type*} [Fintype I] [Fintype O]
    [Nonempty I] [Nonempty O] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Entanglement.IsCompletelyPositive M ↔ (outputFirstChoi M).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
