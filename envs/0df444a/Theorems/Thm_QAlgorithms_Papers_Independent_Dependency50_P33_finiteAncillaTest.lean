-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P33_finiteAncillaTest
-- name    : QAlgorithms.Papers.Independent.Dependency50.P33.finiteAncillaTest
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:21:16.300498+00:00
-- url     : https://prove2.me/theorems/b9366868-4682-4424-8976-e6c52254c1ba
-- title:
--   Finite-dimensional ancillas suffice to test entanglement breaking
-- statement:
--   Let $H$ and $H'$ be nonzero separable complex Hilbert spaces and let $\Phi:\mathfrak T(H)\to\mathfrak T(H')$ be a complex-linear, completely positive, trace-preserving channel. A channel is entanglement-breaking when its output on one factor of every bipartite state is separable. Then
--
--   $$
--   \begin{aligned}
--   &\forall K\text{ separable},\ \forall\omega\in\mathfrak S(H\otimes K),
--   \quad(\Phi\otimes\operatorname{Id}_K)(\omega)\text{ is separable}\\
--   &\quad\Longleftrightarrow\quad
--   \forall n\in\mathbb N,\ \forall\omega\in\mathfrak S(H\otimes\mathbb C^n),
--   \quad(\Phi\otimes\operatorname{Id}_{\mathbb C^n})(\omega)\text{ is separable}.
--   \end{aligned}
--   $$
--
--   All tensor products are completed Hilbert tensor products, and separability means trace-norm closed convex hull of product states. There is no upper bound on the finite test dimension. The zero-dimensional test contains no states and causes no restriction.
--
--   This criterion reduces the ancilla dimensions needed for the definition. The normalized spectral compressions used in the source proof are not hypotheses on the input state.
-- source:
--   Separability and Entanglement-Breaking in Infinite Dimensions, arXiv:quant-ph/0504204v1, PDF p. 3, §3, following Definition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.RealRegisters (Hilbert)

/-- Finite-ancilla test following Definition 2, PDF pp.3–4.
There is no uniform upper bound on the finite ancilla dimension. -/
theorem finiteAncillaTest {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (Phi : (Matrix I I ℂ) → (Matrix J J ℂ)) (hPhi : IsTraceClassChannel Phi) :
    BreaksTraceClassEntanglement Phi ↔
      ∀ (n : ℕ) (rho : State (I × Fin n)),
        IsSeparable (tensorApply Phi rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P33

end
