-- Prove2me | Theorems.Thm_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg
-- name    : ValuationSubring.exists_algebraicIndependent_residue_of_le_trdeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/80146e3b-19fe-512d-853e-838cc94b0636
-- title:
--   Lifting d algebraically independent residues into a valuation ring
-- statement:
--   Let $k$ and $K$ be fields, let $c \colon k \to K$ be a ring homomorphism, and let $O$ be a valuation subring of $K$ such that $c(x) \in O$ for every $x \in k$; thus $c$ corestricts to a ring homomorphism $k \to O$, and composing it with the residue map $O \to \kappa(O) =$ `IsLocalRing.ResidueField O` makes the residue field of the local ring $O$ into a $k$-algebra. Let $d$ be a natural number and assume that, with respect to this $k$-algebra structure, $d$ (viewed as a cardinal) is at most $\operatorname{trdeg}_k \kappa(O)$, the transcendence degree of $\kappa(O)$ over $k$. The conclusion asserts the existence of a family $g \colon \mathrm{Fin}\, d \to K$ together with a proof that $g_i \in O$ for every $i$, such that the family of residues $i \mapsto \overline{g_i} \in \kappa(O)$, formed from the elements $g_i$ regarded as elements of $O$, is algebraically independent over $k$ in the sense of `AlgebraicIndependent`.
--
--   This is the standard statement that a transcendence-degree bound for the residue field of a valuation ring can be realised by elements of the ring itself: $d \le \operatorname{trdeg}_k \kappa(O)$ yields $d$ elements of $O$ with algebraically independent residues. It is used in the construction of a valuation subring of a function field with prescribed behaviour at a point whose local ring has Krull dimension one, in [`AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one`](thm.html#AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ValuationSubring.exists_algebraicIndependent_residue_of_le_trdeg
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ}
    (hd :
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      (d : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O)) :
    ∃ (g : Fin d → K) (hg : ∀ i, g i ∈ O),
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩) := by sorry
