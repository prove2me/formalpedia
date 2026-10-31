-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P10_translatedCechCocycle
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P10.translatedCechCocycle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:39:34.991201+00:00
-- url     : https://prove2.me/theorems/deec7c54-3c69-4b5f-af42-daeb3c1dde41
-- title:
--   The translated-cover smooth Cech cocycle and its independence of representative
-- statement:
--   Let $G$ be a connected Hausdorff locally convex real Lie group with identity $e$ and let $Z=\mathfrak z/\Gamma$, where $\mathfrak z$ is sequentially complete and Hausdorff locally convex and $\Gamma$ is discrete. Give $Z$ the quotient Lie structure and the trivial $G$-action. Let $f:G\times G\to Z$ be a normalized locally smooth central two-cocycle. Suppose $f$ is smooth on $U\times U$, and choose an open symmetric identity neighborhood $V\subseteq U$ with $V^2\subseteq U$. On the open cover $(gV)_{g\in G}$ the functions
--
--   $$
--   \tau(f)_{g,h}(x)=f(g,g^{-1}x)-f(h,h^{-1}x),\qquad x\in gV\cap hV,
--   $$
--
--   are smooth and satisfy $\tau(f)_{g,h}-\tau(f)_{g,k}+\tau(f)_{h,k}=0$ on triple overlaps. They therefore define a smooth Cech cohomology class in $\check H^1(G,Z)$.
--
--   If $f'$ represents the same locally smooth group-cohomology class as $f$, shrink $U,V$ to common neighborhoods for $f,f'$ and a normalized cochain $b$ smooth near the identity with $f(g,h)-f'(g,h)=b(g)-b(gh)+b(h)$. Then
--
--   $$
--   [\tau(f)]=[\tau(f')],\qquad
--   \tau(f)_{g,h}-\tau(f')_{g,h}=c_g-c_h,\quad
--   c_g(x)=b(g)+b(g^{-1}x).
--   $$
--
--   Each $c_g$ is smooth on $gV$. This gives the representative-independent characteristic cocycle used to describe the underlying extension bundle.
--
--   **Formalization Note** Equality in local group cohomology is unpacked into its defining witness $b$ on common shrunken neighborhoods. Cech classes themselves are actual quotients over open covers and refinements.
-- source:
--   Non-integral central extensions of loop groups, arXiv:0910.1937v1, PDF p. 4, Lemma 2.2: the translated-cover Cech cocycle

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

/-- Lemma 2.2, PDF p. 4 (with standing assumptions on pp. 1–2): the
 translated-cover formula is a smooth Cech cocycle and its Cech class is
 unchanged by a normalized locally smooth coboundary. Comparisons use a
 common shrunken U and V, exactly as in the source proof. The equality of
 local group-cohomology classes is unpacked into its defining witness b
 from (1.1); it is not replaced by an arbitrary cohomology carrier.
 The printed proof's alternative formula has its sign reversed: the correct
 rewrite is f(g,g⁻¹h)-f(g⁻¹h,h⁻¹x). The stated tau formula is unchanged. -/
theorem translatedCechCocycle
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
    ∃ htau : IsSmoothCechCocycle (E := E) (F := F)
        (translatedCover V hV hVOne) (translatedTau (G := G) f),
      ∀ (fOther : G → G → F ⧸ Gamma) (b : G → F ⧸ Gamma),
        NormalizedTwoCocycle fOther →
        SmoothOn (E := E × E) (F := F) (U ×ˢ U)
          (fun p : G × G => fOther p.1 p.2) →
        b 1 = 0 → SmoothOn (E := E) (F := F) U b →
        (∀ g h, f g h - fOther g h = b g - b (g * h) + b h) →
        ∃ htauOther : IsSmoothCechCocycle (E := E) (F := F)
            (translatedCover V hV hVOne) (translatedTau (G := G) fOther),
          cechClass (CechRepresentative.mk
            (translatedCover V hV hVOne) (translatedTau (G := G) f) htau) =
          cechClass (CechRepresentative.mk
            (translatedCover V hV hVOne) (translatedTau (G := G) fOther) htauOther) ∧
          (∀ g, SmoothOn (E := E) (F := F) (translatedOpen V g)
            (translatedComparison b g)) ∧
          (∀ g h x, x ∈ translatedOpen V g → x ∈ translatedOpen V h →
            translatedTau f g h x - translatedTau fOther g h x =
              translatedComparison b g x - translatedComparison b h x) := by sorry

end Statement

end QAlgorithms.Papers.Independent.Intakenext100.P10
