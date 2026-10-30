-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_inducedOrbitOptima
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.inducedOrbitOptima
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:48:49.313737+00:00
-- url     : https://prove2.me/theorems/3372b578-5233-4c4f-be3a-caa02080b9dc
-- title:
--   §III.C: induced functions preserve optimum, (63)–(67)
-- statement:
--   Let a finite-dimensional real Lie group $G$ act smoothly from the right on a finite-dimensional smooth manifold $M$. Fix $x\in M$ and a smooth function $F:M\to\mathbb R$. Define $f(g)=F(x\cdot g)$ and $\widehat f=F|_{\mathcal O(x)}$. Then
--   $$\{f(g):g\in G\}=\{\widehat f(y):y\in\mathcal O(x)\}.$$
--   An element $g$ attains a global maximum on $G$ exactly when $x\cdot g$ attains one on the orbit. Also $f(hg)=f(g)$ whenever $x\cdot h=x$, and equal orbit points give equal objective values. This expresses the stabilizer-coset descent while avoiding an unwarranted assertion that a maximum exists.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 14, §III.C: induced functions preserve optimum, (63)–(67)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Induced orbit objective and attained-optimum correspondence (63)--(67),
PDF p.14. Equality of value sets avoids assuming a maximum exists. -/
theorem inducedOrbitOptima
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G M : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [IsManifold 𝓘(ℝ, E) ∞ G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [T2Space G] [SecondCountableTopology G]
    [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (alpha : M → G → M)
    (hsmooth : ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : M × G => alpha p.1 p.2))
    (hone : ∀ x, alpha x 1 = x)
    (hmul : ∀ x g h, alpha (alpha x g) h = alpha x (g * h))
    (quality : M → ℝ) (hquality : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ quality) (x : M) :
    let f : G → ℝ := fun g => quality (alpha x g)
    let fhat : Set.range (alpha x) → ℝ := fun y => quality y.val
    Set.range f = Set.range fhat ∧
    (∀ g, (∀ h, f h ≤ f g) ↔ ∀ y : Set.range (alpha x), fhat y ≤ f g) ∧
    (∀ h g, alpha x h = x → f (h * g) = f g) ∧
    (∀ g h, alpha x g = alpha x h → f g = f h) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
