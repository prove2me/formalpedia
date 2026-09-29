-- Prove2me | Theorems.Thm_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three
-- name    : TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/31ff45db-c863-55a2-92f7-c9aff4fd98b1
-- title:
--   Galois-equivariant parametrisation of the Tate curve's 3-torsion
-- statement:
--   Let $p$ be a prime with $p = 3$, and let $q_T \in \mathbb{Q}_p$ be nonzero with $\|q_T\|_+ < 1$. Write $E_{q_T}$ for the Weierstrass curve [`TateCurve.curve qT`](def/TateCurve_QSeries.html#L185), namely the curve with coefficients $(a_1,a_2,a_3,a_4,a_6) = (1,0,0,a_4(q_T),a_6(q_T))$ built from the $q$-series of the Tate parametrisation, and consider its group of points over $\overline{\mathbb{Q}}_p =$ `AlgebraicClosure ℚ_[p]`. The assertion is that there exist $\zeta, t \in \overline{\mathbb{Q}}_p$ such that $\zeta$ is a primitive $p$-th root of unity and $t^p$ equals the image of $q_T$ under the structure map $\mathbb{Q}_p \to \overline{\mathbb{Q}}_p$, together with a bijection $\varphi \colon \mathbb{Z}/p \times \mathbb{Z}/p \to E_{q_T}[p](\overline{\mathbb{Q}}_p)$, the latter being the $\mathbb{Z}$-submodule of points killed by $p$, with the following two properties: $\varphi$ is additive, in the sense that the underlying points satisfy $\varphi(a+b) = \varphi(a) + \varphi(b)$ for all $a,b$; and $\varphi$ is Galois-equivariant in the form that for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ and all $e, c \in \mathbb{N}$ with $\sigma\zeta = \zeta^e$ and $\sigma t = \zeta^c t$, one has $\sigma \cdot \varphi(i,j) = \varphi(e \cdot i + c \cdot j,\, j)$ for all $i, j \in \mathbb{Z}/p$.
--
--   This is the description of the $p$-torsion of the Tate curve over a $p$-adic field, with its Galois action in the standard basis coming from $\mu_p$ and from a $p$-th root of the Tate parameter, specialised to $p = 3$; the resulting Galois module is upper-triangular with the cyclotomic character on the quotient fixed by the second coordinate. It is used in [`WeierstrassCurve.exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_eq_three`](thm.html#WeierstrassCurve.exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_eq_three), where the local parametrisation is transported to the $3$-torsion of an elliptic curve with multiplicative reduction. The proof cites the existence of a complete algebraically closed isometric extension of $\mathbb{Q}_p$, a Kummer–Hopf parametrisation over $\mathbb{Z}_p$, and the count $\#E[n] = n^2$ over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three.lean

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal WeierstrassCurve.Affine

theorem TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three
    (p : ℕ) [Fact p.Prime] (hp3 : p = 3) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (ζ t : AlgebraicClosure ℚ_[p]), IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
    ∃ φ : (ZMod p × ZMod p) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      (∀ a b, (φ (a + b) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              = (φ a : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              + (φ b : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
        σ ζ = ζ ^ e → σ t = ζ ^ c * t →
        ∀ i j : ZMod p, σ • (φ (i, j)) = φ (e • i + c • j, j) := by sorry
