-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_finiteCopyCorrelation
-- name    : QAlgorithms.Papers.Independent.Information100.P08.finiteCopyCorrelation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:11:25.347792+00:00
-- url     : https://prove2.me/theorems/29180bd6-b479-4d7a-8af4-6b3c59157aba
-- title:
--   Finite-copy measurement-correlation bound
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. For a state $\rho_{AB}$ and integer $n\ge1$, let $J_n(\rho)$ be the supremum of $I(X;B^n)$ over all finite measurements on Alice's $A^n$ in $\rho_{AB}^{\otimes n}$. Then $$J_n(\rho)\le nV_F^{\to}(\rho).$$ This is a finite-copy measurement-correlation bound, including $n=1$, without any strong-superadditivity assumption.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 39, Finite-copy measurement-correlation bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.39, (9.18): finite-copy correlation bound, including n=1, without strong superadditivity. -/
theorem finiteCopyCorrelation {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (n : ℕ) (hn : 1 ≤ n) :
    copyCorrelation n rho ≤ n * statePotential rho := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
