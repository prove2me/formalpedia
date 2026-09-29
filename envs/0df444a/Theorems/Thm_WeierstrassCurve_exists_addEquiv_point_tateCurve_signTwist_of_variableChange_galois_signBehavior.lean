-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
-- name    : WeierstrassCurve.exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/c48ecf5b-a98f-5e68-a6fb-2bc3b6c5dacc
-- title:
--   Sign-twisted point isomorphism W(ℚ̄ₚ)≅ E_{q_T}(ℚ̄ₚ)
-- statement:
--   Fix a Weierstrass curve $W$ over $\mathbb{Z}$, a prime $p$ (with a decidable equality instance on $\overline{\mathbb{Q}_p} =$ `AlgebraicClosure ℚ_[p]`), a parameter $q_T \in \mathbb{Q}_p$, an element $s \in \overline{\mathbb{Q}_p}$, and a variable change $C$ over $\overline{\mathbb{Q}_p}$. Two hypotheses are imposed. First, $C$ carries the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}_p \to \overline{\mathbb{Q}_p}$ to the base change of the Tate curve $y^2 + xy = x^3 + a_4(q_T)x + a_6(q_T)$, i.e. of the Weierstrass curve [`TateCurve.curve`](def/TateCurve_QSeries.html#L185) $q_T$ with coefficients $(1,0,0,a_4(q_T),a_6(q_T))$. Second, for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$, the coefficientwise image $\sigma(C)$ equals $C$ when $\sigma s = s$, and equals $\langle -1,0,-1,0\rangle \cdot C$ (the variable change with $u=-1$, $r=0$, $s=-1$, $t=0$) when $\sigma s \neq s$. The conclusion asserts an isomorphism of abelian groups $\psi$ between the group of $\overline{\mathbb{Q}_p}$-points of the affine model of $W_{\mathbb{Q}_p}$ and that of [`TateCurve.curve`](def/TateCurve_QSeries.html#L185) $q_T$, such that for every such $\sigma$ and every point $P$ one has $\psi(\sigma \cdot P) = \sigma \cdot \psi(P)$ if $\sigma s = s$, and $\psi(\sigma \cdot P) = -(\sigma \cdot \psi(P))$ otherwise.
--
--   This is the transport of a Galois-sign-behaved variable change to the level of points: the $\overline{\mathbb{Q}_p}$-points of $W$ are identified with those of the Tate curve $E_{q_T}$ equivariantly up to the quadratic sign character cut out by the orbit of $s$, so that a Tate parametrisation of $W$ becomes available after a sign twist. It is cited by the corresponding statement for the $p$-torsion subgroup, [`WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior`](thm.html#WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior), which is what feeds into the local description of the mod $p$ representation at a prime of multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior.lean

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ_[p])]
    (qT : ℚ_[p])
    (s : AlgebraicClosure ℚ_[p])
    (C : VariableChange (AlgebraicClosure ℚ_[p]))
    (hC : C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
          = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
    (hCσ : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
        (σ s ≠ s → C.map σ.toAlgHom.toRingHom
          = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C)) :
    ∃ ψ : ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point
          ≃+ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point,
      ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → ∀ P, ψ (σ • P) = σ • ψ P) ∧
        (σ s ≠ s → ∀ P, ψ (σ • P) = -(σ • ψ P)) := by sorry
