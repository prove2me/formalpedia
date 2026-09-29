-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring
-- name    : WeierstrassCurve.Affine.exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/fe15e6df-d969-525d-aba3-4c73d4ece29c
-- title:
--   Weil pairing of integral torsion points lies in a valuation subring
-- statement:
--   Let $K$ be an algebraically closed field, $\mathcal O \subseteq K$ a valuation subring, $\Omega$ a further algebraically closed field (in the same universe), and $\psi : \mathcal O \to \Omega$ a ring homomorphism. Let $W$ be a Weierstrass curve over $\mathcal O$ that is elliptic, and let $n$ be a natural number whose image in $\mathcal O$ is a unit. Let $x_S, y_S, x_T, y_T \in \mathcal O$ be such that $(x_S,y_S)$ and $(x_T,y_T)$, mapped along $\mathcal O \hookrightarrow K$, are nonsingular points of the curve over $K$ obtained from $W$, and likewise, mapped along $\psi$, are nonsingular points of the curve over $\Omega$ obtained from $W$; assume each of the four resulting affine points $S_K, T_K, S_\Omega, T_\Omega$, viewed in the respective groups of points, is killed by $n$. Then there exists $u \in \mathcal O$ whose image in $K$ is the scalar $\mathrm{weilPairing0}$ attached to $(S_K, T_K)$ on the curve over $K$ and whose image under $\psi$ is the scalar $\mathrm{weilPairing0}$ attached to $(S_\Omega, T_\Omega)$ on the curve over $\Omega$. Here $\mathrm{weilPairing0}\,W\,K\,n\,S\,T$ is, by definition, a unit $c \in K^\times$ with $\tau_S^{*} f_{n,T} = c \cdot f_{n,T}$ in the function field, where $f_{n,T}$ is the ratio of the Weil numerators at $T$ and at $0$ and $\tau_S$ is translation by $S$ (`transEquiv`), such a $c$ being chosen if one exists and $1$ otherwise.
--
--   This is the compatibility of the Weil pairing with base change in the two cases of interest: invariance under a homomorphism of algebraically closed fields, and compatibility with reduction, packaged as integrality of the pairing of torsion points with coordinates in a valuation subring. It is used in the study of level components of modular curves, where a pairing value must be recognised simultaneously over a generic and a special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)
    (W : WeierstrassCurve 𝒪) [W.IsElliptic] (n : ℕ) (hn : IsUnit ((n : ℕ) : (𝒪 : Type u)))
    (xS yS xT yT : 𝒪)
    (hSK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xS) (algebraMap 𝒪 K yS))
    (hTK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT))
    (hSΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xS) (ψ yS))
    (hTΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xT) (ψ yT))
    (hSKn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hSK = 0)
    (hTKn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTK = 0)
    (hSΩn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hSΩ = 0)
    (hTΩn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTΩ = 0) :
    ∃ u : 𝒪, algebraMap 𝒪 K u =
        ((weilPairing0 (W.map (algebraMap 𝒪 K)) K n (WeierstrassCurve.Affine.Point.some _ _ hSK)
          (WeierstrassCurve.Affine.Point.some _ _ hTK) : Kˣ) : K) ∧
      ψ u = ((weilPairing0 (W.map ψ) Ω n (WeierstrassCurve.Affine.Point.some _ _ hSΩ)
          (WeierstrassCurve.Affine.Point.some _ _ hTΩ) : Ωˣ) : Ω) := by sorry
