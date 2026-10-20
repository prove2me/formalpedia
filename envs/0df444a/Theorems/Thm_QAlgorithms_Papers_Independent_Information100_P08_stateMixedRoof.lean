-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_stateMixedRoof
-- name    : QAlgorithms.Papers.Independent.Information100.P08.stateMixedRoof
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:05:37.29658+00:00
-- url     : https://prove2.me/theorems/977e9941-1f9f-4327-a0ff-7089d5ece3aa
-- title:
--   Proposition 9.1: mixed-roof representation
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. For a state $\sigma_{BE}$, $J(E;B)_\sigma$ is the supremum of outcome–$B$ mutual information over finite POVMs on $E$, and $G_E(\sigma)$ is its convex roof over decompositions into possibly mixed states. For any purification $\psi_{ABE}$ of $\rho_{AB}$, let $\rho_{BE}=\operatorname{Tr}_A\psi$. Then $$V_F^{\to}(\rho_{AB})=S(B)_\rho-G_E(\rho_{BE}).$$ The retained instrument output may include every local dilation system. This represents the potential without assuming measurement attainment.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 38, Proposition 9.1: mixed-roof representation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.38, Proposition 9.1: state potential equals the environment-measured mixed roof;
all local dilation systems are available to Alice's instrument. -/
theorem stateMixedRoof {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (psi : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ)
    (hpure : IsPure psi) (hpurifies : traceRight psi = rho) :
    statePotential rho = vnEntropy (traceLeft rho) - environmentRoof (complementaryMarginal psi) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
