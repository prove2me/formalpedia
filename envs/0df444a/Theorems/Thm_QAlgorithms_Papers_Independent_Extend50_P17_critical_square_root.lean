-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_critical_square_root
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.critical_square_root
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:03:03.723777+00:00
-- url     : https://prove2.me/theorems/b5598e18-220c-4cc6-a3f4-1d6508691e71
-- title:
--   Corollary 19 / Eq.(76): critical square-root limit
-- statement:
--   Let $0<a<1$, and let $k(N)$ be an integer schedule with $1\le k(N)\le N$ eventually and $k(N)/\sqrt N\to a$. For optimal conclusive qubit MPBT with fixed maximally entangled resource,
--
--   $$\lim_{N\to\infty}p_{\rm succ}(N,k(N))=2\int_0^\infty\frac{x^2}{\sqrt{2\pi}}e^{-(x+a)^2/2}\,dx.$$
--
--   Integer schedules implement the stated square-root scaling without requiring an impossible exact equality for every natural $N$. This preserves the numbered corollary's narrower parameter range and does not assume a finite-size sandwich.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 16, Corollary 19 / Eq.(76): critical square-root limit

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.16, Corollary 19, Eq.(76): preserve its narrower 0<a<1 scope. -/
theorem critical_square_root (k : ℕ → ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hphysical : ∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N)
    (hscale : Tendsto (fun N => (k N : ℝ) / Real.sqrt N) atTop (nhds a)) :
    Tendsto (fun N => mpbtSuccessProbability 2 N (k N)) atTop (nhds (gaussianLimit a)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
