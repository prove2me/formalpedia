-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_compatible_optimalCores
-- name    : QAlgorithms.Papers.Independent.Information100.P07.compatible_optimalCores
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:42:24.791972+00:00
-- url     : https://prove2.me/theorems/a106cf98-0da5-462f-a346-8f760b842821
-- title:
--   Unnumbered: optimal separable decompositions compatible with the given channels
-- statement:
--   Let entangled two-qutrit states $\rho,\sigma$ be interconverted by given separable CPTP channels $\Lambda,\Psi$. Define $b(\rho)$ as the maximum trace of a separable positive operator $S\le\rho$, and $F_\rho$ as the set of maximizers. Both optimizer sets are nonempty, compact and convex, and their weights agree. For $\Omega=\Psi\Lambda$, $S_0\in F_\rho$, and $n\ge1$, the Cesaro averages $\bar S_n=n^{-1}\sum_{k=0}^{n-1}\Omega^k(S_0)$ lie in $F_\rho$ and satisfy
--   $$\|\Omega(\bar S_n)-\bar S_n\|_1\le2b/n.$$
--   There exists $S_*\in F_\rho$ fixed by $\Omega$, with $S'=\Lambda(S_*)\in F_\sigma$. For $t=1-b>0$, the residual states $\delta=(\rho-S_*)/t$, $\delta'=(\sigma-S')/t$ have CES ranges and satisfy $\Lambda(\delta)=\delta'$, $\Psi(\delta')=\delta$, $\Psi(S')=S_*$.
--
--   This chooses compatible optimizers and does not impose compatibility on every optimizer.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 16, Unnumbered: optimal separable decompositions compatible with the given channels

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.16, Eqs.(S28)–(S31): compatible optimizers for the given separable channels. -/
theorem compatible_optimalCores (rho sigma : Joint) (hr : Entangled rho) (hs : Entangled sigma)
    (Phi Psi : Superop (Fin 3 × Fin 3) (Fin 3 × Fin 3))
    (hPhi : SeparableChannel Phi) (hPsi : SeparableChannel Psi)
    (hforward : Phi rho = sigma) (hreverse : Psi sigma = rho) :
    (optimalSet rho).Nonempty ∧ IsCompact (optimalSet rho) ∧ Convex ℝ (optimalSet rho) ∧
    (optimalSet sigma).Nonempty ∧ IsCompact (optimalSet sigma) ∧ Convex ℝ (optimalSet sigma) ∧
    bestSeparableWeight rho = bestSeparableWeight sigma ∧ 0 < 1 - bestSeparableWeight rho ∧
    (∀ S ∈ optimalSet rho, ∀ n : ℕ, 0 < n → cesaro (Psi ∘ Phi) S n ∈ optimalSet rho ∧
      traceNorm (Psi (Phi (cesaro (Psi ∘ Phi) S n)) - cesaro (Psi ∘ Phi) S n) ≤
        2 * bestSeparableWeight rho / n) ∧
    ∃ S ∈ optimalSet rho, Psi (Phi S) = S ∧ Phi S ∈ optimalSet sigma ∧
      let t := 1 - bestSeparableWeight rho
      let delta := ((t : ℂ)⁻¹) • (rho - S)
      let zeta := ((t : ℂ)⁻¹) • (sigma - Phi S)
      IsDensityMatrix delta ∧ IsDensityMatrix zeta ∧ IsCES (operatorRange delta) ∧ IsCES (operatorRange zeta) ∧
      Phi delta = zeta ∧ Psi zeta = delta := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
