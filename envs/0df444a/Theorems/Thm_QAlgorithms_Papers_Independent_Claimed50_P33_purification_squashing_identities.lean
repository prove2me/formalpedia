-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_purification_squashing_identities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.purification_squashing_identities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:45:13.498988+00:00
-- url     : https://prove2.me/theorems/268014a2-f7ad-4e3c-bc13-dfaad4eb5c4b
-- title:
--   §IV.G equation (58): extension/channel infimum identities
-- statement:
--   Let $m\ge2$, let $\rho$ be a normalized state on finite nonzero local spaces, and fix a finite nonzero register $R$ and a vector $\psi$ with $\|\psi\|=1$ and $\operatorname{Tr}_R|\psi\rangle\langle\psi|=\rho$. Every normalized extension $\omega$ on a positive finite-dimensional register $E$ has the form $\omega=(\operatorname{id}\otimes\Lambda)(|\psi\rangle\langle\psi|)$ for a CPTP map $\Lambda:R\to E$. Consequently, simultaneously for total and dual conditional correlations in bits,
--
--   $$\frac12\inf_{\substack{e\ge1,\ \omega\ge0,\ \operatorname{Tr}\omega=1\\\operatorname{Tr}_E\omega=\rho}}F(A_1:\cdots:A_m\mid E)_\omega
--   =\inf_{\substack{e\ge1\\\Lambda:R\to E\ \mathrm{CPTP}}}\frac12F(A_1:\cdots:A_m\mid E)_{(\operatorname{id}\otimes\Lambda)(|\psi\rangle\langle\psi|)}.$$
--
--   All positive finite output dimensions occur; $R$ is fixed before both infima. The half normalization is an explicitly named rescaling of Definition 3. This supplies the finite-dimensional supporting interface; no infinite-dimensional entropy subtraction is asserted.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 7, §IV.G equation (58): extension/channel infimum identities

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Equation (58), PDF p.7: all extensions are CPTP images of the FIXED
normalized purification. Both total and dual HALF-infima agree with the
all-channel versions. No output-dimension bound or channel restriction.
The common 1/2 explicitly rescales Definition 3, p.4. Finite dimensions only. -/
theorem purification_squashing_identities {m : ℕ} (hm : 2 ≤ m)
    {D : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {R : Type} [Fintype R] [Nonempty R]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (RegisterBasis D × R)) (hpsi : ‖psi‖ = 1)
    (hmarginal : forgetEnvironment (pureDensity psi) = rho) :
    (∀ e : ℕ, 0 < e → ∀ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma → forgetEnvironment sigma = rho →
      ∃ Phi : Superop R (Fin e), IsChannel Phi ∧
        sigma = idTensorSuperop Phi (pureDensity psi)) ∧
    (halfExtensionSquashed .total rho = halfChannelSquashed .total psi) ∧
    (halfExtensionSquashed .dual rho = halfChannelSquashed .dual psi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
