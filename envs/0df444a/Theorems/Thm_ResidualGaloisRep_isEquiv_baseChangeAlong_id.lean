-- Prove2me | Theorems.Thm_ResidualGaloisRep_isEquiv_baseChangeAlong_id
-- name    : ResidualGaloisRep.isEquiv_baseChangeAlong_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7a9fea40-0ec4-5bc9-b3da-585f7a673dc4
-- title:
--   Base change along the identity preserves a residual representation
-- statement:
--   Let $k$ be a field and let $\rho$ be a residual Galois representation over $k$ in the sense of the project, that is: a $k$-vector space $V$ with $\dim_k V = 2$, together with a monoid homomorphism $\rho \colon \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to \mathrm{End}_k(V)$ which factors through a finite level, meaning that there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $L/\mathbb{Q}$ finite such that every automorphism fixing $L$ pointwise is sent to $1$. The assertion is that $\rho$ is equivalent to its base change along the identity ring homomorphism of $k$, where the base change along a ring homomorphism $\psi \colon k \to k'$ is the representation with carrier $k' \otimes_k V$ (for the algebra structure induced by $\psi$) and operators $\sigma \mapsto (\rho(\sigma)) \otimes \mathrm{id}$, and where equivalence means the existence of a $k$-linear isomorphism between the underlying spaces intertwining the two actions of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$. Concretely: there is a $k$-linear isomorphism $V \to k \otimes_k V$ commuting with the Galois operators on both sides.
--
--   This is bookkeeping for the base-change construction on residual representations: it identifies $\rho$ with $\rho$ base changed along the identity, via the unit isomorphism $V \cong k \otimes_k V$, so that hypotheses phrased through a base change along `RingHom.id` can be read as hypotheses on $\rho$ itself. It is used in the Hecke-algebra step [`CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd`](thm.html#CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isEquiv_baseChangeAlong_id.lean

import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.isEquiv_baseChangeAlong_id {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsEquiv (ρ.baseChangeAlong (RingHom.id k)) := by sorry
