-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_probabilistic_scaling
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.probabilistic_scaling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:56:27.27949+00:00
-- url     : https://prove2.me/theorems/85466482-d3eb-4d8f-820f-b47c1f364000
-- title:
--   Eq.(15) / Table 3: MPBT probabilistic scaling law
-- statement:
--   Let $k(N)$ be integers with $1\le k(N)\le N$ eventually. For the optimal conclusive qubit protocol with fixed maximally entangled resource, write $p_{\rm succ}(N,k)$ for its success probability and define
--
--   $$G(a)=2\int_0^\infty\frac{x^2}{\sqrt{2\pi}}e^{-(x+a)^2/2}\,dx.$$
--
--   For any $a>0$, $k(N)/\sqrt N\to a$ implies $p_{\rm succ}(N,k(N))\to G(a)$. If $k(N)/\sqrt N\to0$, this probability tends to $1$. This states both branches of Eq. (15) and the subcritical case Eq. (16), using integer schedules rather than generally impossible exact equalities. In addition, Table 3 gives the supercritical regime: for $a>0$ and $1/2<\alpha\le1$, if $k(N)/N^\alpha\to a$, then $p_{\rm succ}(N,k(N))\to0$. The eventual physical bounds on $k$ still apply; no equal-package divisibility is imposed on MPBT.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 6, Eq.(15) / Table 3: MPBT probabilistic scaling law

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Eqs.(15)–(16) and Table 3: critical, subcritical, and supercritical
limits for physical integer schedules. The zero limit is stated for the table's
power scaling, with 1/2 < alpha ≤ 1 and positive scaling coefficient. -/
theorem probabilistic_scaling (k : ℕ → ℕ)
    (hphysical : ∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) :
    (∀ a : ℝ, 0 < a →
      Tendsto (fun N => (k N : ℝ) / Real.sqrt N) atTop (nhds a) →
      Tendsto (fun N => mpbtSuccessProbability 2 N (k N)) atTop (nhds (gaussianLimit a))) ∧
    (Tendsto (fun N => (k N : ℝ) / Real.sqrt N) atTop (nhds 0) →
      Tendsto (fun N => mpbtSuccessProbability 2 N (k N)) atTop (nhds 1)) ∧
    (∀ a alpha : ℝ, 0 < a → (1/2 : ℝ) < alpha → alpha ≤ 1 →
      Tendsto (fun N : ℕ => (k N : ℝ) / (N : ℝ)^alpha) atTop (nhds a) →
      Tendsto (fun N => mpbtSuccessProbability 2 N (k N)) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
