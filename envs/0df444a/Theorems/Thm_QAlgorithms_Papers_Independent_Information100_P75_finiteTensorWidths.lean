-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_finiteTensorWidths
-- name    : QAlgorithms.Papers.Independent.Information100.P75.finiteTensorWidths
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:09:13.692005+00:00
-- url     : https://prove2.me/theorems/046c5780-89cd-43df-a65e-5c492df07f71
-- title:
--   Finite tensor widths for subspaces and matrices
-- statement:
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $N\ge1$ and $n_i\ge1$ for $i=1,\ldots,N$. For complex linear subspaces $\mathcal A_i\subset M_{n_i}(\mathbb C)$ and, separately, matrices $X_i\in M_{n_i}(\mathbb C)$, one has both identities
--
--   $$
--   \operatorname{sw}^*\!\left(\bigotimes_{i=1}^N\mathcal A_i\right)=\min\left\{\sum_{i=1}^N\operatorname{sw}^*(\mathcal A_i),\pi\right\},\qquad
--   \operatorname{sw}\!\left(\bigotimes_{i=1}^NX_i\right)=\min\left\{\sum_{i=1}^N\operatorname{sw}(X_i),\pi\right\}.
--   $$
--
--   The subspace product denotes the span of all corresponding simple tensors. These identities extend saturated additivity to any positive finite list of systems.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 4, Corollary 4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Corollary 4, PDF p.4: both subspace and individual-matrix identities.
The list is nonempty and every system dimension is positive. -/
theorem finiteTensorWidths {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℕ) (hd : ∀ i, 0 < d i) :
    (∀ M : (i : Fin N) → Submodule ℂ (Mat (Fin (d i))),
      infWidth (listTensorSpace d M) = min (∑ i, infWidth (M i)) Real.pi) ∧
    (∀ X : (i : Fin N) → Mat (Fin (d i)),
      width (listTensor d X) = min (∑ i, width (X i)) Real.pi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
