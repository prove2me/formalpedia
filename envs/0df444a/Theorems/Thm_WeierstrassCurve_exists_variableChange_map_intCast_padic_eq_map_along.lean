-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along
-- name    : WeierstrassCurve.exists_variableChange_map_intCast_padic_eq_map_along
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/bef096a6-e6b0-5e0f-aa1b-2ded744bfce9
-- title:
--   Two ℚₚ-models of E agree up to variable change
-- statement:
--   Let $R$ be a commutative ring which is a domain, equipped with an algebra structure over $\mathbb{Q}$ exhibiting $\mathbb{Q}$ as its fraction field. Let $E$ be a Weierstrass curve over $\mathbb{Q}$ and $W_0$ a Weierstrass curve over $R$ whose base change to $\mathbb{Q}$ (the coefficientwise image under $\mathrm{algebraMap}\,R\,\mathbb{Q}$) is equal to $E$. Let $W$ be a Weierstrass curve over $\mathbb{Z}$ which is an integral model of $E$ in the sense of the project predicate `IsIntegralModelOf`, i.e. there is a variable change $C_0$ over $\mathbb{Q}$ with $C_0 \bullet E = W \otimes_{\mathbb{Z}} \mathbb{Q}$ (the coefficientwise image of $W$ under $\mathbb{Z} \to \mathbb{Q}$). Let $p$ be a prime and $f \colon R \to \mathbb{Z}_p$ a ring homomorphism such that for every $r \in R$ the image of $f(r)$ in $\mathbb{Q}_p$ coincides with the image of $r$ under $R \to \mathbb{Q} \to \mathbb{Q}_p$. The conclusion is that there exists a variable change $C$ over $\mathbb{Q}_p$ with $C \bullet \bigl((W_0 \otimes_{R,f} \mathbb{Z}_p) \otimes_{\mathbb{Z}_p} \mathbb{Q}_p\bigr) = W \otimes_{\mathbb{Z}} \mathbb{Q}_p$, the two base changes being taken coefficientwise.
--
--   This is a compatibility statement between the two ways of producing a $\mathbb{Q}_p$-model of an elliptic curve $E/\mathbb{Q}$: pushing an abstract $R$-model forward along $R \to \mathbb{Z}_p$ and then inverting $p$, versus reducing a $\mathbb{Z}$-integral model to $\mathbb{Q}_p$; both are $\mathbb{Q}_p$-forms of $E$ and so differ by an admissible change of variables. It is used in the construction of the $p$-adic torsion comparison in [`WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along`](thm.html#WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in

theorem WeierstrassCurve.exists_variableChange_map_intCast_padic_eq_map_along
    (R : Type) [CommRing R] [IsDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) (W₀ : WeierstrassCurve R) (heq : W₀⁄ℚ = E)
    {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (f : R →+* ℤ_[p])
    (hfc : ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r)) :
    ∃ C : WeierstrassCurve.VariableChange ℚ_[p],
      C • ((W₀.map f)⁄ℚ_[p]) = W.map (Int.castRingHom ℚ_[p]) := by sorry
