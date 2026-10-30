-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P10_proposition11_wPlus_hilbertSchmidt_lower_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P10.proposition11_wPlus_hilbertSchmidt_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:23:19.701637+00:00
-- url     : https://prove2.me/theorems/1338f592-2443-4ede-ab09-a84c79e312c0
-- title:
--   Universal W+ lower bound by squared Hilbert–Schmidt distance
-- statement:
--   Let $m$ be a nonnegative integer and let $\rho_0,\rho_1$ be arbitrary states on the completed $m$-mode oscillator Hilbert space: positive trace-class operators of trace one. Use $\hbar=1$ and the Wigner normalization $W_I=(2\pi)^{-m}$. A binary measurement $(M,I-M)$ belongs to $W+$ when both effects have nonnegative Wigner symbols. Define $\|\rho_0-\rho_1\|_{W+}$ as twice the supremum of $\operatorname{Tr}[(\rho_0-\rho_1)M]$ over these effects. With $\Delta=\rho_0-\rho_1$, one has
--
--   $$
--   \|\rho_0-\rho_1\|_{W+}\ge 2^{-m-1}\|\Delta\|_2^2
--   =2^{-m-1}\operatorname{Tr}(\Delta^2).
--   $$
--
--   Here $\|\Delta\|_2$ is the Hilbert–Schmidt norm. Its square is the finite nonnegative trace of the composed operator $\Delta^2$, because $\Delta$ is self-adjoint and trace-class. No energy bound or nonnegative-Wigner hypothesis on the input states is required. This guarantees nonzero $W+$ distinguishability for every distinct state pair.
--
--   **Formalization Note** The squared Hilbert–Schmidt quantity is represented directly by the accepted infinite-dimensional operator trace and composition. The claim is about $W+$, not GOCC.
-- source:
--   Bosonic data hiding: power of linear vs non-linear optics, arXiv:2102.01622v1, PDF p. 8, Proposition 11, (49)–(50)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P10

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P10

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeOperator PhaseVector FockWeylSystem numberBasis numberKet)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass operatorTrace State)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

/-- Proposition 11, arXiv:2102.01622v1, PDF p.8, (49)–(50).
All full m-mode states are allowed, with no energy or Wigner positivity
hypothesis. For the self-adjoint trace-class difference Delta, the squared
Hilbert–Schmidt norm is the finite nonnegative trace Tr(Delta composed with
Delta), represented by the accepted operatorTrace, not by a matrix trace. -/
theorem proposition11_wPlus_hilbertSchmidt_lower_bound {m : ℕ}
    (W : FockWeylSystem m) (rho0 rho1 : State (numberBasis m)) :
    ((2 : ℝ) ^ (m + 1))⁻¹ *
      (operatorTrace (numberBasis m)
        ((rho0.val.val - rho1.val.val).comp (rho0.val.val - rho1.val.val))).re ≤
      wPlusDistance W rho0 rho1 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P10

end
