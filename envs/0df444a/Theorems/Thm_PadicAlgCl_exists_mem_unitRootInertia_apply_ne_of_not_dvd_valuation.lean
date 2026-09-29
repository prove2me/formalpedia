-- Prove2me | Theorems.Thm_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
-- name    : PadicAlgCl.exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/8ca34203-2807-5ea8-aab1-448b95f9040e
-- title:
--   Unit-root inertia moves p-th roots of valuation prime to p
-- statement:
--   Let $p$ be a prime, let $x \in \mathbb{Q}_p$ be such that $p$ does not divide the integer valuation $v(x)$ of $x$, and let $\gamma$ be an element of the algebraic closure $\overline{\mathbb{Q}}_p$ (the type `PadicAlgCl p`) with $\gamma^p = x$, the equality being taken after applying the structure map $\mathbb{Q}_p \to \overline{\mathbb{Q}}_p$. The assertion is that there exists an element $\tau$ of the local Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ (the group `primeLocalGaloisGroup (pPrime p)`, whose elements act through `localAut p` as $\mathbb{Q}_p$-algebra automorphisms) satisfying the three conditions defining [`ResidualGaloisRep.unitRootInertia p`](def/GaloisRep_OrdinaryUnitClasses.html#L17), namely: $\tau$ lies in the inertia subgroup attached to the valuation subring of the canonical rank-one valuation on $\overline{\mathbb{Q}}_p$, pushed forward from the decomposition subgroup into the full automorphism group; $\tau$ fixes every $\zeta \in \overline{\mathbb{Q}}_p$ with $\zeta^p = 1$; and $\tau$ fixes every $\beta \in \overline{\mathbb{Q}}_p$ of norm $\|\beta\|=1$ whose $p$-th power $\beta^p$ is fixed by every element of that inertia subgroup — and such that nevertheless $\tau \gamma \neq \gamma$.
--
--   In classical terms the fixed field of `unitRootInertia` is $\mathbb{Q}_p^{\mathrm{nr}}(\zeta_p, (\mathcal{O}^{\mathrm{nr},\times})^{1/p})$, and the statement says that the Kummer class of an $x$ with $p \nmid v(x)$ is très ramifié in Serre's sense: its $p$-th roots do not lie in that field. It is used in bounding the space of cocycles cut out by the unit-root inertia condition, in the local analysis of ordinary deformation classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem PadicAlgCl.exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : ¬ (p : ℤ) ∣ Padic.valuation x)
    (γ : PadicAlgCl p) (hγ : γ ^ p = algebraMap ℚ_[p] (PadicAlgCl p) x) :
    ∃ τ ∈ ResidualGaloisRep.unitRootInertia p, ResidualGaloisRep.localAut p τ γ ≠ γ := by sorry
