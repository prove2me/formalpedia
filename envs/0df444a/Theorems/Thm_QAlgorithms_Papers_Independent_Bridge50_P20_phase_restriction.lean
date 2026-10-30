-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_phase_restriction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.phase_restriction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:07:19.048196+00:00
-- url     : https://prove2.me/theorems/cde6613b-cbd2-4ed7-a423-ed518c481e70
-- title:
--   Invariant two-qubit family for both separable optimizations
-- statement:
--   For a normalized two-qubit state $\rho$ invariant under $U_\theta=e^{i(\theta/2)\sigma_z}\otimes e^{-i(\theta/2)\sigma_z}$, both separable-comparison optimizations in Proposition 1 may be restricted to the following family, in basis order $00,01,10,11$:
--
--   $$
--   \sigma(p)=\frac12\begin{pmatrix}\alpha&0&0&\xi e^{i\varphi}\\0&\gamma&0&0\\0&0&\delta&0\\\xi e^{-i\varphi}&0&0&\beta\end{pmatrix},\quad
--   \alpha,\beta,\gamma,\delta,\xi\ge0,\quad\alpha+\beta+\gamma+\delta=2,\quad
--   0\le\varphi\le2\pi,\quad\xi\le\min\{\sqrt{\alpha\beta},\sqrt{\gamma\delta}\}.
--   $$
--
--   Precisely, these are exactly the separable fixed points of normalized angular averaging, and the infimal divergence over either original feasible set equals the infimal divergence over this family. The additional constraint $\operatorname{Tr}_B\sigma=I/2$ holds exactly when $\gamma=1-\alpha$ and $\delta=1-\beta$. This reduction uses the two-qubit PPT characterization and does not extend it to arbitrary dimensions.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 28, Appendix B, unnumbered corollary, (B6): invariant-state reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1707.05543v2, PDF p.28, unnumbered corollary (B6): both minima
reduce to the displayed two-qubit family; that family exactly describes the
separable fixed points of the twirl, and its marginal equations are explicit. -/
theorem phase_restriction (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hrho : IsDensityMatrix rho) (hinv : IsPhaseInvariant rho) :
    (∀ fixed : Bool, comparisonMinimum rho fixed =
      sInf {v : EReal | ∃ p : PhaseParameters, p.Valid ∧
        (fixed = true → p.FixedMarginal) ∧ v = maxRelative rho (invariantSeparableMatrix p)}) ∧
    (∀ sigma : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      (IsSeparableDensity sigma ∧ phaseTwirl sigma = sigma) ↔
        ∃ p : PhaseParameters, p.Valid ∧ sigma = invariantSeparableMatrix p) ∧
    (∀ p : PhaseParameters, p.Valid →
      (traceRight (invariantSeparableMatrix p) = mixedIdentity (Fin 2) ↔ p.FixedMarginal)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
