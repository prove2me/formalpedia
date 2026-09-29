-- Prove2me | Theorems.Thm_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le
-- name    : ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/19853fa0-c568-56b2-925e-4dde93c619d0
-- title:
--   Flat bound for H¹_f(ℚₚ,adρ̄), p odd
-- statement:
--   Let $k$ be a finite field, $p$ an odd prime with $k$ of characteristic $p$, and let $\bar\rho$ be a [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22) over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\operatorname{End}_k V$ that is trivial on the automorphisms fixing some finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$. Write $G_p$ for the group of $\mathbb{Q}_p$-algebra automorphisms of an algebraic closure of $\mathbb{Q}_p$, mapped to the global Galois group by restriction of scalars followed by restriction to $\overline{\mathbb{Q}}$, and let $\operatorname{ad}\bar\rho$ be the representation of the global group on $\operatorname{End}_k V$ by $f \mapsto \rho(\sigma) f \rho(\sigma^{-1})$, restricted along that map. The hypothesis is that the zero cocycle satisfies `IsLocallyFlatCocycleAd`: there is a commutative ring $H$ with a cocommutative Hopf $\mathbb{Z}_p$-algebra structure, finite and flat as a $\mathbb{Z}_p$-module, and a bijection $e$ from the $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}}_p$, with their convolution group law, onto $V \times V$, which is additive and carries the natural $G_p$-action $f \mapsto \sigma \circ f$ to the diagonal action $(x_1,x_2) \mapsto (\rho(\sigma)x_1,\rho(\sigma)x_2)$. Then the subspace $H^1_f \subseteq H^1(G_p,\operatorname{ad}\bar\rho)$ spanned by the classes of the $1$-cocycles $c$ satisfying `IsLocallyFlatCocycleAd` (for $c$, the second coordinate of the action being twisted by $c(\sigma)$) is finite-dimensional over $k$, and $\dim_k H^1_f \le \dim_k (\operatorname{ad}\bar\rho)^{G_p} + 1$.
--
--   This is the local computation at $p$ underlying the flat deformation condition: the tangent space of the finite flat deformation problem for $\bar\rho|_{G_p}$ has dimension at most $1 + \dim_k H^0(\mathbb{Q}_p,\operatorname{ad}\bar\rho)$, the bound used in comparing Selmer groups with the flat condition at $p$. Only the inequality is asserted, not the equality that holds in the Fontaine–Laffaille range. It is used by the corresponding bound for the full space of local flat classes, [`ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le.lean

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

theorem ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) (hflat : ρbar.IsLocallyFlatCocycleAd p 0) :
    FiniteDimensional k (ρbar.localFlatClassesAd p) ∧
      Module.finrank k (ρbar.localFlatClassesAd p) ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants + 1 := by sorry
