-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_fourier_block_classification
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.fourier_block_classification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:39:42.465303+00:00
-- url     : https://prove2.me/theorems/036e0410-8ce9-4c0b-96a1-ee3fc39d0752
-- title:
--   Fourier blocks classify equivariant linear layers and their dimension
-- statement:
--   Fix a symmetric group $S_n$ and finite-dimensional real activation spaces $E,H$, with linear representations $A,B$. Choose a finite family of pairwise inequivalent nonzero real irreducible models $\rho_a$ of dimensions $d_a$. Let $\tau_a,\tau'_a$ be nonnegative multiplicities, and let $U,V$ be actual invertible linear changes of coordinates that intertwine $A,B$ with left action by $\rho_a$ on every column of the respective $d_a\times\tau_a$ and $d_a\times\tau'_a$ blocks. Then a real linear map $L:E\to H$ is equivariant if and only if there is a unique family of real matrices $W_a\in\mathbb R^{\tau_a\times\tau'_a}$ such that, for every input $x$,
--
--   $$
--   [V(Lx)]_a=[Ux]_aW_a.
--   $$
--
--   Moreover, the vector space of these equivariant linear maps has dimension
--
--   $$
--   \dim_{\mathbb R}\operatorname{Hom}_{S_n}(E,H)=\sum_a\tau_a\tau'_a.
--   $$
--
--   This classifies the learnable linear operation before the fixed nonlinearity. The dimension counts linear maps, independently of any loss of information caused by that nonlinearity.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 4, Theorem 3 (§4): Fourier block classification and exact parameter count; headline selected from the paper-level seed

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 3, source PDF p.4, with exact parameter count on p.4–5.
The actual invertible intertwining Fourier maps are inputs, not the classification
being asserted. Irreducible labels may be reindexed without changing the claim.
No unitary diagonalization of arbitrary nonorthogonal representations is asserted. -/
theorem fourier_block_classification {n : ℕ} {I E H : Type*} [Fintype I]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup H] [Module ℝ H] [FiniteDimensional ℝ H]
    (A : Perm n →* Module.End ℝ E) (B : Perm n →* Module.End ℝ H)
    (d tau upsilon : I → ℕ)
    (rho : (a : I) → Perm n →* Module.End ℝ (Fin (d a) → ℝ))
    (hirr : ∀ a, IsRealIrreducible (rho a))
    (hneq : ∀ a b, a ≠ b → ModelsInequivalent (rho a) (rho b))
    (U : E ≃ₗ[ℝ] FourierBlocks d tau) (V : H ≃ₗ[ℝ] FourierBlocks d upsilon)
    (hU : ∀ s x, U (A s x) = fourierColumnAction rho s (U x))
    (hV : ∀ s x, V (B s x) = fourierColumnAction rho s (V x)) :
    (∀ L : E →ₗ[ℝ] H,
      L ∈ equivariantLinearMaps (fun s => A s) (fun s => B s) ↔
        ∃! w : FourierWeights tau upsilon, ∀ x, V (L x) = applyBlocks w (U x)) ∧
    Module.finrank ℝ (equivariantLinearMaps (fun s => A s) (fun s => B s)) =
      ∑ a, tau a * upsilon a := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
