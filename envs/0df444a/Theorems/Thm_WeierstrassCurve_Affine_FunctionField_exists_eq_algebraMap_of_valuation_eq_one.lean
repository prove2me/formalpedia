-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one
-- name    : WeierstrassCurve.Affine.FunctionField.exists_eq_algebraMap_of_valuation_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/3180b122-1bc0-5283-bc24-20ba69c94aeb
-- title:
--   Everywhere trivial valuation forces a constant function
-- statement:
--   Let $F$ be a field and $W$ a Weierstrass curve over $F$, and assume the affine coordinate ring `W.toAffine.CoordinateRing`, i.e. $F[X,Y]$ modulo the Weierstrass polynomial of $W$, is a Dedekind domain. Let $f$ be an element of the function field `W.toAffine.FunctionField`, the fraction field of that coordinate ring. Suppose that for every $v$ in the height-one spectrum of the coordinate ring — that is, every nonzero prime ideal — the associated $v$-adic valuation of $f$, taken in the multiplicative value group $\mathbb{Z}_{m_0}$ attached to $v$ by `IsDedekindDomain.HeightOneSpectrum.valuation`, is equal to $1$; equivalently, $f$ has order $0$ at every such $v$, so neither a zero nor a pole. The conclusion is that there exists $c \in F$ with $c \neq 0$ and $f$ equal to the image of $c$ under the structure map $F \to$ `W.toAffine.FunctionField`. No condition at the point at infinity is imposed.
--
--   This is the form of the classical statement that a rational function on an elliptic curve with trivial divisor is constant (Silverman, AEC II.1.2, II.3.1), phrased purely in terms of the height-one valuations of the affine coordinate ring. It is used in the construction of the Weil pairing, where ratios of translated functions are shown to be constant: among the results citing it are [`WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom`](thm.html#WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom), [`WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_smul`](thm.html#WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_smul) and [`WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq`](thm.html#WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.FunctionField.exists_eq_algebraMap_of_valuation_eq_one {F : Type*} [Field F] {W : WeierstrassCurve F} [IsDedekindDomain W.toAffine.CoordinateRing] {f : W.toAffine.FunctionField} (hf : ∀ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, v.valuation W.toAffine.FunctionField f = 1) : ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.FunctionField c := by sorry
