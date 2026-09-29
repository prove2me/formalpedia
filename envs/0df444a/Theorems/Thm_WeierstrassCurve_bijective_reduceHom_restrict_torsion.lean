-- Prove2me | Theorems.Thm_WeierstrassCurve_bijective_reduceHom_restrict_torsion
-- name    : WeierstrassCurve.bijective_reduceHom_restrict_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/6a46cc65-8303-5013-a723-fbb439951c3b
-- title:
--   Reduction is bijective on N-torsion over a Henselian valuation subring
-- statement:
--   Let $L$ be a field with decidable equality and let $A \subseteq L$ be a valuation subring which, as a local ring, is Henselian and whose residue field is algebraically closed (and has decidable equality). Let $W$ be a Weierstrass curve over $A$, and assume that the Weierstrass curve $W \bmod \mathfrak m$ obtained by applying the residue map $A \to \mathrm{ResidueField}(A)$ to the coefficients of $W$ has nonzero discriminant, $(W.\mathrm{map}\ (\mathrm{residue}\ A)).\Delta \neq 0$. Let $N$ be a natural number whose image in the residue field is nonzero. Consider the base change of $W$ along the inclusion $A \hookrightarrow L$ and the group of affine points $(W.\mathrm{map}\ A.\mathrm{subtype}).\mathrm{toAffine}.\mathrm{Point}$ of the resulting curve over $L$. The assertion is that the map from $\{P : N \cdot P = 0\}$ to $\{Q : N \cdot Q = 0\}$ on the curve $W \bmod \mathfrak m$, sending $P$ to `reduceHom hΔ P`, is bijective. Here `reduceHom hΔ` is the additive homomorphism whose underlying map sends the point at infinity to the point at infinity and an affine point $(x,y)$ with $x \in A$ to $(\bar x, \bar y)$, the residues of $x$ and of $y$ (which lies in $A$ automatically), while points with $x \notin A$ are sent to the point at infinity; it carries $N$-torsion to $N$-torsion because it is additive.
--
--   This is the statement that reduction induces an isomorphism between the $N$-torsion of the generic fibre and that of the special fibre when $N$ is invertible in the residue field, the base is Henselian and the residue field is algebraically closed: injectivity is the classical injectivity of reduction on torsion of order prime to the residue characteristic, and surjectivity is the lifting of torsion points through Hensel's lemma. It is used in the construction of level structures and the comparison of points on fibres of modular curves, and in the identification of reductions of torsion subgroups with kernel polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_bijective_reduceHom_restrict_torsion.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.bijective_reduceHom_restrict_torsion
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [HenselianLocalRing A] [DecidableEq (ResidueField A)]
    [IsAlgClosed (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ}
    (hN : (N : ResidueField A) ≠ 0) :
    Function.Bijective
      (fun P : {P : (W.map A.subtype).toAffine.Point // N • P = 0} =>
        (⟨reduceHom hΔ P.1, by rw [← map_nsmul, P.2, _root_.map_zero]⟩ :
          {Q : (W.map (residue A)).toAffine.Point // N • Q = 0})) := by sorry
