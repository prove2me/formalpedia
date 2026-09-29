-- Prove2me | Theorems.Thm_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
-- name    : ResidualGaloisRep.isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/b521dd78-8a84-5dea-878e-2460c942607c
-- title:
--   Local flatness of a cocycle forces flatness of ρ̄⊕ρ̄
-- statement:
--   Let $k$ be a field, $p$ a prime with $p \neq 2$, and let $\bar\rho$ be a residual representation over $k$, that is, a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k V$ that is trivial on the elements fixing some finite subextension of $\overline{\mathbb Q}/\mathbb Q$. Let $c$ be a $1$-cocycle of the local group $\mathrm{Aut}_{\mathbb Q_p}(\overline{\mathbb Q}_p)$, acting through the homomorphism `primeLocalToGlobal` to the global Galois group, with values in $\mathrm{ad}^0\bar\rho$, the trace-zero endomorphisms of $V$ under conjugation by $\rho$. Assume `ρbar.IsLocallyFlatCocycle p c`: there are a commutative ring $H$ carrying a cocommutative Hopf algebra structure over $\mathbb Z_p$, finite and flat as a $\mathbb Z_p$-module, and a bijection $e$ from the convolution monoid of $\mathbb Z_p$-algebra maps $H \to \overline{\mathbb Q}_p$ onto $V \times V$ with $e(f \ast g) = e(f) + e(g)$, such that whenever $g = \sigma \circ f$ pointwise one has $e(g) = (\rho(\sigma)x_1,\ c(\sigma)(\rho(\sigma)x_1) + \rho(\sigma)x_2)$ for $e(f) = (x_1,x_2)$. The conclusion is the same assertion for the zero cocycle with values in $\mathrm{ad}\,\bar\rho$: some finite flat cocommutative $\mathbb Z_p$-Hopf algebra has its points, with convolution, additively and equivariantly identified with $V \times V$ under the diagonal action $(x_1,x_2) \mapsto (\rho(\sigma)x_1, \rho(\sigma)x_2)$.
--
--   This is the schematic-closure step in the study of locally flat deformation conditions at $p$: a finite flat model of the dual-lift module $V \oplus \varepsilon V$ attached to a locally flat cocycle yields one for $V \oplus V$ with the diagonal action, so that $\bar\rho$ restricted to the decomposition group at $p$ is itself finite flat. It is used in [`ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le), where the space of local flat classes is shown to vanish in the degenerate case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero))
    (hc : ρbar.IsLocallyFlatCocycle p c) :
    ρbar.IsLocallyFlatCocycleAd p 0 := by sorry
