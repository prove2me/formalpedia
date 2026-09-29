-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_map_eq_of_act_relabel_eq
-- name    : WeierstrassCurve.DrinfeldGlobal.map_eq_of_act_relabel_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/1ac30997-883b-5713-b359-4520f1452211
-- title:
--   Relabelling fixing a Drinfeld basis reduces to ± 1
-- statement:
--   Let $A$ be a commutative ring and $\mathcal G$ a discriminant-guarded family of relative group laws, assigning to every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta_W$ is a unit a relative group law on the projective model of $W$. Assume $\mathcal G$ is chord–tangent (for all such $T,W$ there is an equivalence $ev$ between sections over field-valued points and the points of the affine curve which exhibits the group law as the chord–tangent law) and has the origin as identity (the identity section is cut out by a ring map from the origin chart sending $x/y$ and $z/y$ to $0$). Let $q$ be a prime, $\mathcal T$ a level-transport datum for $(A,\mathcal G,q)$ — functorial base-change maps and variable-change actions on raw Drinfeld pairs, unital and multiplicative, commuting with base change and preserving the level-$q$ condition — and assume $\mathcal T$ is a section transport, i.e. both actions are pinned: the transported sections, composed with the comparison isomorphism of curves and with $\mathrm{Proj}$ of any graded realiser, recover the original sections. Assume further that every variable change $C$ over every $A$-algebra admits a graded ring map $\varphi$ between the graded projective-model rings whose image's irrelevant ideal dominates the target's and which implements the substitutions $X_0 \mapsto u^2X_0 + rX_2$, $X_1 \mapsto u^3X_1 + u^2sX_0 + tX_2$, $X_2 \mapsto X_2$, fixing constants. Let $K$ be a field which is an $A$-algebra with $q \neq 0$ in $K$, $W$ a projective Weierstrass curve over $K$, and $x$ a raw Drinfeld pair over $K$ (a curve $x.\mathrm{curve}$ together with two sections $P,Q$) with $\Delta_{x.\mathrm{curve}}$ a unit and $x$ of level $q$ for $W$, meaning $x.\mathrm{curve} = W$ and $(P,Q)$ is a Drinfeld basis of level $q$ for $\mathcal G\,K\,x.\mathrm{curve}$. Let $g$ be a $2\times 2$ integer matrix and $C$ a variable change over $K$ such that acting by $C$ on the relabelled pair, whose curve is unchanged and whose sections are the group-law combinations $g_{00}P + g_{10}Q$ and $g_{01}P + g_{11}Q$, returns $x$. Then: if $C = 1$, the reduction of $g$ modulo $q$ is the identity matrix; and if $C = (-1, 0, -a_1, -a_3)$ with $a_1,a_3$ the coefficients of $x.\mathrm{curve}$, the reduction of $g$ modulo $q$ is $-1$.
--
--   This is the rigidity step for $\Gamma(q)$-level structures: an integral relabelling matrix that carries a Drinfeld basis back to itself, up to the trivial change of variables or the negation $[-1]$, is congruent to $\pm 1$ modulo $q$, so the relabelling action on bases is faithful only through $\mathrm{GL}_2(\mathbb Z/q)$ up to sign. It feeds the computation of the stabiliser of a full-level point under the $\Gamma_0$-type subgroup used in the moduli description of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_map_eq_of_act_relabel_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem WeierstrassCurve.DrinfeldGlobal.map_eq_of_act_relabel_eq
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (K : Type) [Field K] [Algebra A K] (hqK : (q : K) ≠ 0)
    (W : WeierstrassCurve.Projective K) (x : RawDrinfeldPair K) (hΔ : IsUnit x.curve.Δ)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q W x)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (C : WeierstrassCurve.VariableChange K)
    (h : 𝒯.act C (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ) = x) :
    (C = 1 → g.map (Int.castRingHom (ZMod q)) = 1) ∧
      (C = ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ → g.map (Int.castRingHom (ZMod q)) = -1) := by sorry
