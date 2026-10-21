-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_weak_approximate_identity_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P06.weak_approximate_identity_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:43:08.748988+00:00
-- url     : https://prove2.me/theorems/859907e8-5e85-427a-86b6-0fd5571f70e1
-- title:
--   Lemma 7.1
-- statement:
--   Let $F$ be a commutative unital complex algebra, $X$ a complex Banach space, $\Phi:F\to\mathcal C(X)$ a proto-calculus, and $(e_n)$ a weak approximate identity for $f\in F$. Set $D=\operatorname{span}\bigcup_n\operatorname{ran}\Phi(e_n)$. Then $\{e_n:n\in\mathbb N\}$ is an anchor, $D$ is dense and contained in $\operatorname{dom}\Phi(f)$, and $\Phi(f)$ is densely defined. The space $D\cap\operatorname{dom}\Phi(f)$ is a graph core. For a strong approximate identity, $\Phi(e_n)x\to x$ in the graph norm for every $x\in\operatorname{dom}\Phi(f)$. Finally,
--
--   $$\overline{\Phi(e_n)\Phi(f)}=\Phi(e_nf)=\Phi(fe_n)=\Phi(f)\Phi(e_n)\qquad(n\in\mathbb N).$$
--
--   Only the first product is closed in this display. The printed $f_n$ is interpreted as the fixed $f$, as in the source proof.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 18, Lemma 7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Lemma 7.1, PDF pp.18–19: all four parts, with graph closure on the FIRST
product in (d). Printed: fn although only f is fixed. Changed: f. Why: the
proof works with that fixed f. The graph-norm assertion is expressed as
convergence of graph pairs. The correction needs independent moderation. -/
theorem weak_approximate_identity_properties [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (hcomm : ∀ f g : F, f * g = g * f) (f : F) (e : ℕ → F)
    (he : WeakApprox Phi e f) :
    AnchorSet Phi (Set.range e) ∧
    Dense (approximateRangeSpan Phi e) ∧ approximateRangeSpan Phi e ⊆ graphDomain (Phi f) ∧
    Dense (graphDomain (Phi f)) ∧ GraphCore (Phi f) (graphDomain (Phi f) ∩ approximateRangeSpan Phi e) ∧
    (StrongApprox Phi e f → ∀ x y, (x, y) ∈ Phi f →
      Tendsto (fun n => (graphValue (Phi (e n)) x, graphValue (Phi (e n)) y)) atTop (𝓝 (x, y))) ∧
    (∀ n, closure (graphMul (Phi (e n)) (Phi f)) = Phi (e n * f) ∧
      Phi (e n * f) = Phi (f * e n) ∧ Phi (f * e n) = graphMul (Phi f) (Phi (e n))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
