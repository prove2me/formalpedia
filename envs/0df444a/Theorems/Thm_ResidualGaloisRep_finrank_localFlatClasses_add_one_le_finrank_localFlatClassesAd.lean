-- Prove2me | Theorems.Thm_ResidualGaloisRep_finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd
-- name    : ResidualGaloisRep.finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/c74e37ac-2f61-5c3d-97fd-646d27a8dcaf
-- title:
--   Local flat classes: from ad⁰ to ad, one dimension gained
-- statement:
--   Let $k$ be a field in which $2 \neq 0$, let $p$ be a prime, and let $\bar\rho$ be a residual Galois representation over $k$ in the sense of the project: a $k$-vector space $V$ of dimension $2$ together with a monoid homomorphism $\bar\rho \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k(V)$ that is trivial on the subgroup fixing some finite subextension of $\overline{\mathbb Q}/\mathbb Q$. Write $\Gamma_p$ for the automorphism group of the algebraic closure $\mathrm{PadicAlgCl}\,p$ of $\mathbb Q_p$, mapped to the global Galois group by `primeLocalToGlobal`, and let $\mathrm{ad}$ denote the conjugation representation $\sigma \mapsto (f \mapsto \bar\rho(\sigma) f \bar\rho(\sigma)^{-1})$ on $\mathrm{End}_k(V)$ and $\mathrm{ad}^0$ its subrepresentation on the kernel of the trace, both restricted along `primeLocalToGlobal` to $\Gamma_p$. Two hypotheses are imposed: first, the zero $1$-cocycle of $\Gamma_p$ with values in $\mathrm{ad}$ is locally flat, i.e. there is a finite flat cocommutative Hopf algebra $H$ over $\mathbb Z_p$ and a bijection $e$ from the $\mathbb Z_p$-algebra homomorphisms $H \to \mathrm{PadicAlgCl}\,p$, with their convolution product, to $V \times V$ carrying this product to addition and intertwining the Galois action on homomorphisms with the action `dualLiftModuleActAd` attached to the zero cocycle; second, the space $H^1_f(\Gamma_p,\mathrm{ad})$ — the $k$-span inside $H^1(\Gamma_p,\mathrm{ad})$ of the classes of locally flat cocycles in this sense — is finite-dimensional. The conclusion is that the analogously defined span $H^1_f(\Gamma_p,\mathrm{ad}^0)$ of classes of locally flat cocycles with values in $\mathrm{ad}^0$ is finite-dimensional and that $\dim_k H^1_f(\Gamma_p,\mathrm{ad}^0) + 1 \le \dim_k H^1_f(\Gamma_p,\mathrm{ad})$.
--
--   This is the local comparison at $p$ between the flat subspaces of $H^1$ for the trace-zero adjoint and for the full adjoint, the extra dimension being accounted for by a scalar flat class. It feeds the finiteness and dimension bound [`ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le) used in the local bookkeeping of the deformation-theoretic Selmer group estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd.lean

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

theorem ResidualGaloisRep.finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (p : ℕ) [Fact p.Prime]
    (ρbar : ResidualGaloisRep k) (hflat : ρbar.IsLocallyFlatCocycleAd p 0)
    (hfin : FiniteDimensional k (ρbar.localFlatClassesAd p)) :
    FiniteDimensional k (ρbar.localFlatClasses p) ∧
      Module.finrank k (ρbar.localFlatClasses p) + 1 ≤
        Module.finrank k (ρbar.localFlatClassesAd p) := by sorry
