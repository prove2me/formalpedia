-- Prove2me | Theorems.Thm_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform
-- name    : V3Glue.ChartInput.exists_iso_geometricFibre_strictTransform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/38d295d5-d84b-5628-901a-e2d834f2d0a3
-- title:
--   Base change of a glued component is isomorphic to R
-- statement:
--   Let $X$ be a scheme and $C : \mathrm{ChartInput}\,X\,N$ a chart datum: nodes $C.x\,n$, the open set $C.X0$ of points different from every node, étale charts $C.f\,n$ from $C.U\,n$ to model schemes $C.S\,n$, proper resolutions $C.\rho\,n : C.\mathrm{Res}\,n \to C.S\,n$, and structure morphisms to a base $C.B$ with $C.\pi X : X \to C.B$. Assume: `hRF`, that each residue field map of $C.f\,n$ at `C.xU n` is an isomorphism; points `gRes n k` of $C.\mathrm{Res}\,n$, indexed by $k \in \mathrm{Fin}(C.\mathrm{thick}\,n - 1)$, lying over the vertex $C.\mathrm{vertex}\,n = (C.f\,n)(C.\mathrm{xU}\,n)$; two points $\xi_0,\xi_1 \in C.X0$; and a fixed $j \in \mathrm{Fin}\,2$. Write $C_j$ for `(C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme`, the closed subscheme of the glued scheme `C.toGlueInput.glued` cut out by the vanishing ideal sheaf of the closure of the point `C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)`, with closed immersion `subschemeι` into the glued scheme, and `C.toGlueInput.toDR` for the morphism from the glued scheme to $X$. Further data: a closed immersion $c : R \to X_\kappa$ with $R$ integral; morphisms $\mathrm{bcm} : X_\kappa \to X$, $p_2 : X_\kappa \to B_\kappa$, $b : B_\kappa \to C.B$ forming a pullback square with $C.\pi X$; the requirement that $\xi_j$ be the image under $c$ followed by $\mathrm{bcm}$ of the generic point of $R$; the descent identity $\mathrm{bcm}^{-1}\bigl(\overline{\mathrm{bcm}(\mathrm{range}\,c)}\bigr) = \mathrm{range}\,c$; a point $pt \in C.B$ with $\{pt\}$ closed, $\mathrm{range}\,\mathrm{bcm} = C.\pi X^{-1}(\{pt\})$, and every point of $R$ mapping to $pt$; closed immersions $\mathrm{lam}\,n : F\,n \to C.\mathrm{Res}\,n$ such that $\mathrm{lam}\,n$ followed by $C.\rho\,n$ is again a closed immersion and each $\mathrm{pullback}\,(C.g\,n)\,(\mathrm{lam}\,n)$ is reduced; the two-way orientation condition that for $y \in C.U\,n$ one has $(C.f\,n)(y) \in \mathrm{range}(\mathrm{lam}\,n \text{ followed by } C.\rho\,n)$ if and only if $y \in \mathrm{range}(c \text{ followed by } \mathrm{bcm})$, together with $C.x\,n$ lying in that range for every $n$; an index $n_0$; a monomorphism $i : B_0 \to C.B$ and a flat $a : B_\kappa \to B_0$ with $b = a$ followed by $i$; a morphism $s_0 : C_j \to B_0$ through which `subschemeι` followed by `C.toGlueInput.toDR` followed by $C.\pi X$ factors via $i$; and reducedness of the base change along $b$ of $\mathrm{pullback}\,(C.g\,n_0)\,(\mathrm{lam}\,n_0) \to C.B$ (via `pullback.fst` followed by $C.\mathrm{toB}\,n_0 = C.g\,n_0 \gg C.\rho\,n_0 \gg C.\sigma\,n_0$). Then there exists a morphism $e$ from the pullback of `subschemeι ≫ C.toGlueInput.toDR ≫ C.πX` along $b$ to $R$ which is an isomorphism and satisfies: $e$ followed by $c$ and $p_2$ equals the projection `pullback.snd` to $B_\kappa$, and $e$ followed by $c$ and $\mathrm{bcm}$ equals `pullback.fst` followed by `subschemeι` and `C.toGlueInput.toDR`.
--
--   This is the abstract identification of the geometric fibre of a component of the resolved glued model with a prescribed integral closed subscheme $R$ of the geometric fibre of the original model, compatibly with the maps to the base and to $X$; in the intended application $R$ is a component of the geometric fibre of a Deligne–Rapoport model and the component of the glue is its strict transform. It is used by [`V3AsmLevel.strict_iso`](thm.html#V3AsmLevel.strict_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem V3Glue.ChartInput.exists_iso_geometricFibre_strictTransform
    {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (j : Fin 2)

    {R Xκ Bκ : Scheme.{0}} (c : R ⟶ Xκ) [IsClosedImmersion c] [IsIntegral R]
    (bcm : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (b : Bκ ⟶ C.B) (hP : IsPullback bcm p₂ C.πX b)
    (hξj : ξ j = (c ≫ bcm).base (genericPoint R))
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    {pt : C.B} (hpt : IsClosed ({pt} : Set C.B)) (hfib : Set.range bcm.base = C.πX.base ⁻¹' {pt})
    (hcpt : ∀ r : R, (c ≫ bcm ≫ C.πX).base r = pt)

    {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n) [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))]
    (horient_fwd : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base →
      (y : X) ∈ Set.range (c ≫ bcm).base)
    (horient_conv : ∀ n (y : C.U n), (y : X) ∈ Set.range (c ≫ bcm).base →
      (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base)
    (hxim : ∀ n, C.x n ∈ Set.range (c ≫ bcm).base)

    (n₀ : N) {B₀ : Scheme.{0}} (i : B₀ ⟶ C.B) [Mono i] (a : Bκ ⟶ B₀) [Flat a] (hb : b = a ≫ i)
    (s₀ : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme ⟶ B₀)
    (hsB : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX = s₀ ≫ i)
    (hGκ : IsReduced (pullback (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) b)) :
    ∃ e : pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧
        e ≫ c ≫ bcm = pullback.fst _ _ ≫ (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR := by sorry
