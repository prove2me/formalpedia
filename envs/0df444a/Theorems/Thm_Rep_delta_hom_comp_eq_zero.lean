-- Prove2me | Theorems.Thm_Rep_delta_hom_comp_eq_zero
-- name    : Rep.delta_hom_comp_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/c0bda633-e9b7-505d-a533-4e6474065c16
-- title:
--   Vanishing of δ on degree-zero classes from T.X₂
-- statement:
--   Let $G$ be a group and let $R$ be an object of `Rep ℤ G`, that is a representation of $G$ on a $\mathbb{Z}$-module. Let $T$ be a short complex $T.X_1 \xrightarrow{T.f} T.X_2 \xrightarrow{T.g} T.X_3$ in `Rep ℤ G`, and assume the hypothesis `hT` that the short complex obtained by applying the internal hom functor `ihom R` (sending $Y$ to $\mathrm{Hom}(R,Y)$ with the conjugation action) termwise to $T$ is short exact. Let $s : R \to T.X_2$ be a morphism of representations. The class attached to the composite $s$ followed by $T.g$, an element of $\mathrm{Hom}_G(R, T.X_3)$, is formed in two steps: the inverse of `Representation.linHom.invariantsEquivRepHom` identifies it with a $G$-invariant element of $\mathrm{Hom}(R, T.X_3)$, and the inverse of `groupCohomology.H0Iso` identifies the invariants of $(\mathtt{ihom } R).obj\, T.X_3$ with $H^0$ of that representation. The assertion is that the connecting homomorphism `groupCohomology.δ hT 0 1 rfl` from $H^0((\mathtt{ihom } R).obj\, T.X_3)$ to $H^1((\mathtt{ihom } R).obj\, T.X_1)$ sends this class to $0$.
--
--   This is the statement that two consecutive maps of the long exact cohomology sequence of the short exact sequence $(\mathtt{ihom } R)(T)$ compose to zero, namely $\delta \circ (T.g)_* = 0$ in degree $0$, written in terms of equivariant morphisms out of $R$ rather than of cocycles. It is used in the construction of the pairing and nondegeneracy statement [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_delta_hom_comp_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.delta_hom_comp_eq_zero {G : Type} [Group G] (R : Rep ℤ G)
    {T : ShortComplex (Rep ℤ G)} (hT : (T.map (ihom R)).ShortExact) (s : R ⟶ T.X₂) :
    (groupCohomology.δ hT 0 1 rfl).hom
        ((groupCohomology.H0Iso ((ihom R).obj T.X₃)).inv ((Representation.linHom.invariantsEquivRepHom R T.X₃).symm (s ≫ T.g))) = 0 := by sorry
