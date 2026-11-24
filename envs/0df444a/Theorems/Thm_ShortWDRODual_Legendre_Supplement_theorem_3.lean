-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_Supplement_theorem_3
-- name    : ShortWDRODual.Legendre.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:47:16.863619+00:00
-- url     : https://prove2.me/theorems/e9c824c8-f7b7-43c7-86d3-e8ade5520fd0
-- title:
--   Theorem 3 (corrected: (I) has ρ > 0) — both risk-averse transport dualities
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat P)$ be a probability space, let $A$ be a convex subset of an arbitrary real topological vector space, and let $f_\alpha:\mathcal X\to\mathbb R$ be measurable for every $\alpha\in A$, with $\mathbb E_{\widehat P}[f_\alpha]>-\infty$. For each $x$, assume $\alpha\mapsto f_\alpha(x)$ is lower semicontinuous and convex on $A$. On every compact $K\subseteq A$, require one real lower bound for all $f_\alpha(x)$ with $(\alpha,x)\in K\times\mathcal X$. Write $J(P)=\inf_{\alpha\in A}\mathbb E_P[f_\alpha]$.
--
--   1. Let $c:\mathcal X\times\mathcal X\to[0,\infty]$ be measurable, vanish on the diagonal, and have nominal point first. Fix $\rho>0$. Assume $f_\alpha(x)-\lambda c(\hat x,x)$ satisfies the full interchangeability principle, including completed measurability of its pointwise supremum, for every $\lambda>0$ and $\alpha\in A$. Suppose a common compact set $K\subseteq A$ attains $J(P)$ for every probability law in the Kantorovich ball $\mathcal K_c(\widehat P,P)\le\rho$. Then
--
--   $$\mathcal L_J(\rho)=\inf_{\lambda\ge0,\,\alpha\in A}\left\{\lambda\rho+\mathbb E_{\widehat P}\left[\sup_{x\in\mathcal X}\{f_\alpha(x)-\lambda c(\widehat X,x)\}\right]\right\}.$$
--
--   2. Independently, suppose $\mathcal X$ is Polish with its Borel sigma algebra, and let $c:\mathcal X\times\mathcal X\to[0,\infty)$ be continuous and vanish on the diagonal. Fix $\rho\ge0$. Suppose a common compact set $K\subseteq A$ attains $J(P)$ for every probability law in the maximum-cost ball $\overline{\mathcal K}_c(\widehat P,P)\le\rho$. Then
--
--   $$\overline{\mathcal L}_J(\rho)=\inf_{\alpha\in A}\mathbb E_{\widehat P}\left[\sup_x\{f_\alpha(x):c(\widehat X,x)\le\rho\}\right].$$
--
--   These are the two risk-averse dualities (6) and (7). Both final parameter infima range over all of $A$ and need not be attained. The compact witness may differ between branches and radii, but is uniform over the laws within its ball. No global compactness of $A$, joint measurability in $(\alpha,x)$, finite-valued expectation, or finite-dimensional parameter hypothesis is imposed. This is a companion theorem, not a step in the proof of the referenced goal.
--
--   **Formalization Note** The two implications are conjoined; the Polish topology and finite cost belong only to the second. Extended expectations and costs are the immutable published definitions. In particular, $\lambda=0$ remains in the first infimum and $0\cdot\infty=\infty$ for $\lambda c$. The ordinary loss expectations are well-defined because the compact-wise bound applies to each singleton parameter. The nominal expectation assumption is retained as explicitly printed in Assumption 1, although that same lower bound implies it.
--
--   Differences from the source:
--   - correction: Theorem 3 prints no radius restriction; §1 permits zero → (6) is asserted for ρ > 0; (7) is asserted for ρ ≥ 0; reason: Remark 3 (p. 4), specialized to a singleton parameter set, gives L_J(0)=0 but the right side of (6)=1; see DISPROOF.md. No positive radius or case of (II) is excluded.
--   - reading: A is a subset of a linear topological space and α ↦ f_α(x) is convex → ConvexOn ℝ A includes convexity of A, in an arbitrary real topological vector space; reason: This is the usual convex-domain meaning of a convex function; no compactness, finite dimensionality, separation axiom or convexity of the compact witness is added.
--   - encoding: A family f_α indexed by α ∈ A with the compact-wise infimum strictly above −∞ → An ambient family restricted to A, with an explicit real lower bound on each compact K ⊆ A; reason: This is equivalent to the printed lower-bound condition, including empty K. Values of the ambient family outside A are unused.
--   - encoding: Extended-real expectations, nonnegative costs and infima over λ ≥ 0 and α ∈ A → Published extIntegral, transportCost, maxCost, dualG and localSup; complete-lattice infima and an IsLeast formulation of (5); reason: No Bochner default is used. The inherited undefined-expectation convention assigns ∞−∞ to −∞; each f_α is bounded below by the singleton compact case. The λc convention remains 0·∞=∞, and final infima do not claim attainment.
--   - encoding: Two separately conditional parts: (I) on a measurable space; (II) on a Polish Borel space with finite continuous nonnegative cost → A conjunction with separate cost binders and topology assumptions local to (II); reason: This preserves the full measurable-space and possibly infinite-cost domain of (I); no topological or finite-cost premise from (II) is imposed on it.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Theorem 3, equations (6)–(7), p. 11 (PDF p. 11); proof EC.5, pp. ec9–ec10 (PDF pp. 23–24); endpoint correction: Remark 3, p. 4 (PDF p. 4)

import Mathlib
import Definitions.Def_ShortWDRODual_Legendre_Supplement_RobustRisk
import Definitions.Def_ShortWDRODual_Legendre_Supplement_CompactRiskAttainment

namespace ShortWDRODual.Legendre.Supplement

open MeasureTheory ModelRiskOT.Duality

/-- Theorem 3, both clauses, p. 11. In (I) the radius is positive: the source's
Remark 3, p. 4, refutes the zero-radius reading even for a singleton A.
In (II) the radius may be zero. The topology on X is local to clause (II). -/
theorem theorem_3
    {E X : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [MeasurableSpace X]
    (A : Set E) (f : E → X → ℝ) (Phat : Measure X) [IsProbabilityMeasure Phat]
    (hf : ∀ a ∈ A, Measurable (f a))
    (hfint : ∀ a ∈ A, ⊥ < extIntegral Phat (fun x => (f a x : EReal)))
    (hlsc : ∀ x, LowerSemicontinuousOn (fun a => f a x) A)
    (hconvex : ∀ x, ConvexOn ℝ A (fun a => f a x))
    (hlower : ∀ K : Set E, K ⊆ A → IsCompact K →
      ∃ m : ℝ, ∀ a ∈ K, ∀ x : X, m ≤ f a x) :
    (∀ (c : X → X → ENNReal),
      Measurable (fun q : X × X => c q.1 q.2) → (∀ x, c x x = 0) →
      ∀ (rho : ℝ), 0 < rho →
      (∀ (lam : ℝ), 0 < lam → ∀ a ∈ A, IP Phat (phiLam c (f a) lam)) →
      compactRiskAttainment A f
        {P | IsProbabilityMeasure P ∧
          (RWPI.SqrtLasso.transportCost c Phat P : EReal) ≤ (rho : EReal)} →
      robustRisk A f c Phat rho =
        ⨅ (lam : ℝ) (_ : 0 ≤ lam) (a : E) (_ : a ∈ A),
          ((lam * rho : ℝ) : EReal) + dualG c (f a) Phat lam) ∧
    (∀ [tX : TopologicalSpace X] [PolishSpace X] [BorelSpace X]
      (c : X → X → ℝ),
      (∀ x y, 0 ≤ c x y) → Continuous (fun q : X × X => c q.1 q.2) →
      (∀ x, c x x = 0) → ∀ (rho : ℝ), 0 ≤ rho →
      compactRiskAttainment A f
        {P | IsProbabilityMeasure P ∧
          (ShortWDRODual.MaxCost.maxCost c Phat P : EReal) ≤ (rho : EReal)} →
      robustRiskMax A f c Phat rho =
        ⨅ a ∈ A, extIntegral Phat (ShortWDRODual.MaxCost.localSup c (f a) rho)) := by sorry

end ShortWDRODual.Legendre.Supplement
