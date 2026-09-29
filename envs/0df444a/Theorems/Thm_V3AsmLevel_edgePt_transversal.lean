-- Prove2me | Theorems.Thm_V3AsmLevel_edgePt_transversal
-- name    : V3AsmLevel.edgePt_transversal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ee6b9e22-8362-55a6-a97d-4d80c6a94147
-- title:
--   Transversality of adjacent components at edge points
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak X$ be a Deligne–Rapoport model package [`ModularCurve.DRModelPackageLevel`](def/ModularCurve_DRModelPackageLevel.html#L71) for level $(N_0,q)$. Let $O$ be a discrete valuation domain equipped with a ring homomorphism $\rho_O$ from $R q = \mathbb{Q}$-localisation ring [`ModularCurve.DRLevel.R q`](def/ModularCurve_DRModelPackageLevel.html#L32) and with $\mathfrak m_O = (q)$, let $\kappa$ be an algebraically closed field of characteristic $q$ and $\mathrm{to}\kappa : O \to \kappa$, and assume the site hypotheses [`V3AsmLevel.SiteHyps`](def/ModularCurve_ResolvedModelSiteLevel.html#L270) (finiteness of the node set, existence of oriented crossing charts, étale-neighbourhood data, injectivity and closedness of the crossing points, and the hypotheses on the model of $q$ in $O$). Assume further that each of the points $\xi j$ lies in the open `X0` of the chart input $C$, i.e. in the complement of the finitely many marked points of $C$. Then for every node $n$ — a point of the fibre product of the two branch maps $\mathfrak X.\mathrm{comp}\,\kappa\,(\mathrm{to}\kappa \circ \rho_O)\,0$ and $\dots 1$ — and every $d < \mathrm{width}(n)$ (the thickness assigned to $n$ by $C$) there is an affine open $U$ of the glued scheme $Y$ containing the edge point $\mathrm{edgePt}(n,d)$ such that the image, under the germ map $\Gamma(Y,U) \to \mathcal O_{Y,\mathrm{edgePt}(n,d)}$, of the sum of the two sectionwise ideals $\mathrm{comp}(\mathrm{chainPos}(n,d))(U)$ and $\mathrm{comp}(\mathrm{chainPos}(n,d+1))(U)$ is exactly the maximal ideal of $\mathcal O_{Y,\mathrm{edgePt}(n,d)}$. Here $\mathrm{chainPos}$ sends $d = 0$ to the first end component, $0 < d < \mathrm{width}(n)$ to the $(d-1)$-st component of the chain over $n$, and $d \ge \mathrm{width}(n)$ to the second end component, so that for $d = 0$ and for $d + 1 = \mathrm{width}(n)$ one of the two ideals is an end of the chain.
--
--   This is the transversality of the special fibre of the glued resolution at the points where two consecutive components of a chain meet: the local equations of the two components through an edge point generate the maximal ideal of the local ring there. It is one of the field verifications used in the construction of a [`ModularCurve.DRResolvedModelPackageLevel`](def/ModularCurve_DRResolvedModelPackageLevel.html#L41), being cited by [`ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_and_dRResolvedModelChartsLevelRam`](thm.html#ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_and_dRResolvedModelChartsLevelRam).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_V3AsmLevel_edgePt_transversal.lean

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSiteLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3AsmLevel.edgePt_transversal (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∀ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n)), ∃ (U : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).affineOpens) (hU : V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d ∈ (U : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).Opens)),
      Ideal.map ((V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).presheaf.germ (U : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).Opens) (V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d) hU).hom
          ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d)).ideal U ⊔ (V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n (d + 1))).ideal U) =
        IsLocalRing.maximalIdeal ((V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).presheaf.stalk (V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d)) := by sorry
