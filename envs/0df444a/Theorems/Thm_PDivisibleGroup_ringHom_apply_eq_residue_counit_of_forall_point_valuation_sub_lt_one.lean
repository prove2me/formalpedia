-- Prove2me | Theorems.Thm_PDivisibleGroup_ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one
-- name    : PDivisibleGroup.ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/f5718a99-0601-5073-8b1a-d3ca97ea09df
-- title:
--   Residue-field points of a p-divisible level equal the counit
-- statement:
--   Let $p$ be a prime, let $\mathfrak{P}$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `LiesOverPrime p`, i.e. the image of $p$ lies in the non-units of $\mathfrak{P}$, and assume the residue field $\kappa =$ `IsLocalRing.ResidueField ↥Pl` has characteristic $p$ and is algebraically closed. Write $R_D$ for the subring $\mathfrak{P} \cap \overline{\mathbb{Q}}^{D}$, the intersection of $\mathfrak{P}$ with the fixed field of the decomposition subgroup of $\mathfrak{P}$ over $\mathbb{Q}$. Let $\mathcal{T}$ be a $p$-divisible group over $R_D$ of height $t$: a family of finite free cocommutative Hopf $R_D$-algebras $\mathcal{T}.\mathrm{level}\,v$ with $\operatorname{rank}_{R_D} = p^{vt}$, together with surjective coalgebra–algebra transition maps whose kernels are the stated torsion ideals. Assume that every $\overline{\mathbb{Q}}$-point reduces to the counit: for all $v$, every $y \in \mathcal{T}.\mathrm{Point}\,\overline{\mathbb{Q}}\,v$ (an $R_D$-algebra homomorphism $\mathcal{T}.\mathrm{level}\,v \to \overline{\mathbb{Q}}$, with the convolution monoid structure) and every $c$, $\mathfrak{P}$-valuation of $y(c) - \varepsilon(c)$ is $<1$, where $\varepsilon$ is the counit followed by $R_D \to \overline{\mathbb{Q}}$. Then for every $v$ and every ring homomorphism $f : \mathcal{T}.\mathrm{level}\,v \to \kappa$ whose restriction along $R_D \to \mathcal{T}.\mathrm{level}\,v$ is the reduction map $R_D \subseteq \mathfrak{P} \to \kappa$, one has $f(c) = \varepsilon(c) \bmod \mathfrak{m}_{\mathfrak{P}}$ for all $c$.
--
--   This is the statement that if all geometric points of the finite flat levels of a $p$-divisible group over the decomposition ring specialise to the identity, then the special fibre has no $\kappa$-point other than the identity; it is used in the construction of the Raynaud quotient tower attached to the toric part at $p$ of the Néron model of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    {t : ℕ} (𝒯 : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p t)
    (hred : ∀ (v : ℕ) (y : 𝒯.Point (AlgebraicClosure ℚ) v) (c : 𝒯.level v),
      Pl.valuation (PDivisibleGroup.Point.toAlgHom y c -
        algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)
          (Coalgebra.counit c)) < 1)
    (v : ℕ) (f : 𝒯.level v →+* IsLocalRing.ResidueField ↥Pl)
    (hf : f.comp (algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (𝒯.level v)) =
      (IsLocalRing.residue ↥Pl).comp
        ((algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)).codRestrict
          Pl (fun r => r.2.1)))
    (c : 𝒯.level v) :
    f c = IsLocalRing.residue ↥Pl
      ((algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)).codRestrict
        Pl (fun r => r.2.1) (Coalgebra.counit c)) := by sorry
