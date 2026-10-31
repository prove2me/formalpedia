-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P10_twistedExtension_liePrincipalBundle
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P10.twistedExtension_liePrincipalBundle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:38:37.802995+00:00
-- url     : https://prove2.me/theorems/c1a508b4-bf3d-4826-94a3-825136327c4f
-- title:
--   The locally smooth cocycle defines a Lie extension and principal bundle
-- statement:
--   Let $G$ be a connected Hausdorff locally convex real Lie group with identity $e$, let $\mathfrak z$ be a sequentially complete Hausdorff locally convex real space, and let $\Gamma\subseteq\mathfrak z$ be a discrete additive subgroup. Give $Z=\mathfrak z/\Gamma$ its quotient Lie group structure and the trivial $G$-action. Let $f:G\times G\to Z$ be a normalized central two-cocycle, smooth on $U\times U$ for an open identity neighborhood $U$. Choose an open symmetric identity neighborhood $V\subseteq U$ with $V^2\subseteq U$.
--
--   The set $Z\times G$ admits a locally convex Lie group structure whose multiplication and inverse are
--
--   $$
--   (a,g)(b,h)=(a+b+f(g,h),gh),\qquad
--   (a,g)^{-1}=(-a-f(g,g^{-1}),g^{-1}).
--   $$
--
--   Its identity is $(0,e)$, and its smooth structure agrees with the product smooth structure on $Z\times U$. The maps $a\mapsto(a,e)$ and $(a,g)\mapsto g$ give a central Lie group extension and a locally trivial smooth principal $Z$-bundle. Over $gV$ the section is $\sigma_g(x)=(f(g,g^{-1}x),x)$; the corresponding equivariant trivialization sends $(a,x)$ to $(x,a-f(g,g^{-1}x))$.
--
--   This constructs the extension from the given cocycle while retaining the underlying bundle and its explicit local coordinates.
-- source:
--   Non-integral central extensions of loop groups, arXiv:0910.1937v1, PDF p. 4, Section 2, unnumbered: the cocycle twisted Lie extension

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P10

namespace QAlgorithms.Papers.Independent.Intakenext100.P10

open Set Filter Topology

universe u

open QAlgorithms.Papers.Independent.Next46.P35 (DirectionalSmoothOn)

open QAlgorithms.Papers.Independent.Renew46.P29 (LocallyConvexModel NormalizedTwoCocycle)

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P10.centralCoefficientAction

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P10.productCharts

section Statement

variable {E F G : Type u}

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [ChartedSpace E G]

variable (Gamma : AddSubgroup F)

variable [ChartedSpace F (F ⧸ Gamma)]

/-- Section 2, unnumbered construction, PDF pp. 3–4: the specified
 set-theoretic twisted product admits a Lie group structure and is a locally
 trivial principal coefficient bundle. Every multiplication and inverse is
 fixed by f, and the local product structure and all translated bundle
 trivializations are explicit. No paracompactness is imposed.
 The undefined W in the printed V*V subset W is read as U, the next proof's
 local smoothness domain; this does not change the asserted construction. -/
theorem twistedExtension_liePrincipalBundle
    [hConnected : ConnectedSpace G] [hDiscrete : DiscreteTopology Gamma]
    (hG : IsLieGroup E G)
    (hF : LocallyConvexModel ℝ F) (hComplete : SequentiallyComplete F)
    (hCoefficient : QuotientCoefficientAtlas F Gamma)
    (f : G → G → F ⧸ Gamma) (hf : NormalizedTwoCocycle f)
    (U V : Set G) (hU : IsOpen U) (hUOne : (1 : G) ∈ U)
    (hV : IsOpen V) (hVOne : (1 : G) ∈ V)
    (hVU : V ⊆ U) (hSymm : ∀ x ∈ V, x⁻¹ ∈ V)
    (hProduct : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ U)
    (hSmooth : SmoothOn (E := E × E) (F := F) (U ×ˢ U)
      (fun p : G × G => f p.1 p.2)) :
    ∃ groupStructure : Group (TwistedCarrier G (F ⧸ Gamma)),
      letI := groupStructure
      ∃ topology : TopologicalSpace (TwistedCarrier G (F ⧸ Gamma)),
        letI := topology
        ∃ charts : ChartedSpace (F × E) (TwistedCarrier G (F ⧸ Gamma)),
          letI := charts
          IsLieGroup (F × E) (TwistedCarrier G (F ⧸ Gamma)) ∧
          (∀ x y : TwistedCarrier G (F ⧸ Gamma), x * y = twistedCarrierMul f x y) ∧
          (1 : TwistedCarrier G (F ⧸ Gamma)) = ⟨0, 1⟩ ∧
          (∀ x : TwistedCarrier G (F ⧸ Gamma), x⁻¹ = twistedInv f x) ∧
          SmoothOn (E := F × E) (F := E) Set.univ
            (fun x : TwistedCarrier G (F ⧸ Gamma) => x.base) ∧
          SmoothOn (E := F) (F := F × E) Set.univ
            (fun a : F ⧸ Gamma => (⟨a, 1⟩ : TwistedCarrier G (F ⧸ Gamma))) ∧
          (∀ (x : TwistedCarrier G (F ⧸ Gamma)) (a : F ⧸ Gamma),
            x * ⟨a, 1⟩ = ⟨a, 1⟩ * x ∧ x * ⟨a, 1⟩ = coefficientAction x a) ∧
          Function.Surjective (fun x : TwistedCarrier G (F ⧸ Gamma) => x.base) ∧
          (∀ x : TwistedCarrier G (F ⧸ Gamma),
            x.base = 1 ↔ ∃ a : F ⧸ Gamma, x = ⟨a, 1⟩) ∧
          IsOpen {x : TwistedCarrier G (F ⧸ Gamma) | x.base ∈ U} ∧
          SmoothOn (E := F × E) (F := F × E)
            {x : TwistedCarrier G (F ⧸ Gamma) | x.base ∈ U}
            (fun x : TwistedCarrier G (F ⧸ Gamma) => (x.coeff, x.base)) ∧
          SmoothOn (E := F × E) (F := F × E) (Set.univ ×ˢ U)
            (fun p : (F ⧸ Gamma) × G =>
              (⟨p.1, p.2⟩ : TwistedCarrier G (F ⧸ Gamma))) ∧
          ∀ g : G,
            SmoothOn (E := F × E) (F := E × F)
              {x : TwistedCarrier G (F ⧸ Gamma) | x.base ∈ translatedOpen V g}
              (twistedBundleChart f g) ∧
            SmoothOn (E := E × F) (F := F × E)
              (translatedOpen V g ×ˢ Set.univ) (twistedBundleChartInverse f g) ∧
            (∀ x : TwistedCarrier G (F ⧸ Gamma),
              twistedBundleChartInverse f g (twistedBundleChart f g x) = x) ∧
            (∀ p : G × (F ⧸ Gamma),
              twistedBundleChart f g (twistedBundleChartInverse f g p) = p) ∧
            (∀ (x : TwistedCarrier G (F ⧸ Gamma)) (a : F ⧸ Gamma),
              twistedBundleChart f g (coefficientAction x a) =
                ((twistedBundleChart f g x).1, (twistedBundleChart f g x).2 + a)) := by sorry

end Statement

end QAlgorithms.Papers.Independent.Intakenext100.P10
