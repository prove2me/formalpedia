-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaII3
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaII3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:10:51.494778+00:00
-- url     : https://prove2.me/theorems/ac3a5f4c-cf9f-4d2d-81bd-ea0a2469cef3
-- title:
--   Suprema and partial infima preserve convexity
-- statement:
--   Let $S$ be a convex subset of a real vector space and $Y$ an arbitrary set. If every slice $x\mapsto f(x,y)$ of a real-valued function is convex on $S$, then
--   $$g(x)=\sup_{y\in Y}f(x,y)$$
--   is convex in the extended epigraph sense. If $Y$ is also a convex subset of a real vector space and $f$ is jointly convex on $S\times Y$, then
--   $$h(x)=\inf_{y\in Y}f(x,y)$$
--   is convex in the same sense. Empty extrema have their extended values, and unbounded values are not replaced by real default values.
--
--   These closure properties justify convex optimization of families without finiteness assumptions on the indexing set.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 4, Lemma II.3 Let X be a convex set in a vector space and Y be an arbitrary set, and let f : X × Y → R

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)

open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)

open QAlgorithms (spectralProjector)

/-- Lemma II.3, PDF p.4 (9)-(10). Extended epigraphs cover arbitrary, empty,
and unbounded indexing sets. The second clause requires joint convexity. -/
theorem lemmaII3 :
    (∀ (V Y : Type) [AddCommGroup V] [Module ℝ V] (S : Set V) (f : V → Y → ℝ),
      Convex ℝ S → (∀ y, ConvexOn ℝ S (fun x => f x y)) →
      EConvexOn S (fun x => ⨆ y, (f x y : EReal))) ∧
    (∀ (V W : Type) [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
      (S : Set V) (T : Set W) (f : V × W → ℝ),
      Convex ℝ S → Convex ℝ T → ConvexOn ℝ (S ×ˢ T) f →
      EConvexOn S (fun x => ⨅ y : T, (f (x,y.1) : EReal))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
