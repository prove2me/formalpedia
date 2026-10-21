-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P23_varying_exponentials_continuity_and_derivative
-- name    : QAlgorithms.Papers.Independent.Claimed50.P23.varying_exponentials_continuity_and_derivative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:13:06.61998+00:00
-- url     : https://prove2.me/theorems/7660ad09-90d1-4625-b877-538871135284
-- title:
--   Continuity and derivative of varying exponentials
-- statement:
--   Let $\mathfrak g$ be a real Banach--Lie algebra and let $\alpha$ be a strongly continuous, real-linear, bracket-preserving, skew-symmetric representation by complex linear endomorphisms of a dense complex linear subspace $D$ of a complex Hilbert space $H$. Let $I\subseteq\mathbb R$ be an interval and $x:I\to\mathfrak g$ a continuous path. Assume each $\alpha(x(t))$ is essentially skew-adjoint, and write $U_t(s)=e^{s\overline{\alpha(x(t))}}$. Assume $U_t(s)D\subseteq D$ for all $s\in\mathbb R$ and $t\in I$. For every $t\in I$, suppose there exists $\varepsilon_t>0$ such that for every $u\in I$ with $|u-t|<\varepsilon_t$, every $s\in\mathbb R$, and every $v\in D$,
--
--   $$
--   U_t(s)\alpha(x(u))U_t(-s)v
--   =\alpha(e^{s\operatorname{ad}x(t)}x(u))v.
--   $$
--
--   Then for every $v\in D$ the map $(s,t)\mapsto U_t(s)v$ is continuous on $\mathbb R\times I$. If $x$ is differentiable relative to $I$, with actual velocity $\dot x(t)$, then at every parameter with unique relative derivatives the following Banach-valued integral exists and
--
--   $$
--   \frac{d}{dt}U_t(1)v
--   =\alpha\!\left(\int_0^1 e^{s\operatorname{ad}x(t)}\dot x(t)\,ds\right)U_t(1)v.
--   $$
--
--   At non-isolated endpoints the derivative is one-sided. Only differentiability is required, without continuity of the velocity. This result differentiates exponentials whose generators vary along the Lie algebra.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, PDF p. 6, Proposition 10

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23

noncomputable section

open MeasureTheory

open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

section HilbertStatements

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g] [CompleteSpace g]

/-- Proposition 10, PDF pp.6--7: jointly continuous varying exponentials, and
its derivative when the parameter path is differentiable. The local commutation
neighbourhood is chosen before ALL real s. The integral is in g, before alpha
is applied. No C1 hypothesis or invariance beyond the original D is inserted. -/
theorem varying_exponentials_continuity_and_derivative
    [CompleteSpace H] [CompleteSpace g]
    (L : BanachLieBracket g) (D : Submodule ℂ H) (hDense : Dense (D : Set H))
    (alpha : g → D →ₗ[ℂ] D) (hRep : IsStrongRepresentation L D alpha)
    (I : Set ℝ) (hI : Set.OrdConnected I) (x : ℝ → g) (hx : ContinuousOn x I)
    (hA : ∀ t ∈ I, EssentiallySkewAdjoint (onDomain D (D.subtype.comp (alpha (x t)))))
    (hInvariant : ∀ t ∈ I, InvariantDomain D (D.subtype.comp (alpha (x t))))
    (hLocal : ∀ t ∈ I, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ u ∈ I, |u - t| < epsilon → ∀ (s : ℝ) (v : D),
        operatorExp D (D.subtype.comp (alpha (x t))) s
          (alpha (x u) (operatorOrbit D (D.subtype.comp (alpha (x t))) (-s) v) : H) =
        (alpha (adjointExp L s (x t) (x u)) v : H)) :
    (∀ v : D, Continuous (fun p : ℝ × I =>
      operatorExp D (D.subtype.comp (alpha (x (p.2 : ℝ)))) p.1 (v : H))) ∧
    (∀ xVelocity : ℝ → g,
      (∀ t ∈ I, HasDerivWithinAt x (xVelocity t) I t) →
      ∀ (v : D) (t : ℝ), t ∈ I → UniqueDiffWithinAt ℝ I t →
        IntervalIntegrable (fun s : ℝ => adjointExp L s (x t) (xVelocity t)) volume 0 1 ∧
        HasDerivWithinAt
          (fun u : ℝ => operatorExp D (D.subtype.comp (alpha (x u))) 1 (v : H))
          (alpha (∫ s in (0 : ℝ)..1, adjointExp L s (x t) (xVelocity t))
            (operatorOrbit D (D.subtype.comp (alpha (x t))) 1 v) : H) I t) := by sorry

end HilbertStatements

end QAlgorithms.Papers.Independent.Claimed50.P23

end
