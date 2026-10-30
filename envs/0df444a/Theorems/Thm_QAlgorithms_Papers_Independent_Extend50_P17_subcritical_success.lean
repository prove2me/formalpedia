-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_subcritical_success
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.subcritical_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:03:35.506795+00:00
-- url     : https://prove2.me/theorems/b3d5a952-beca-4ae4-befb-083f389dd891
-- title:
--   Corollary 20 / Eq.(77): subcritical success tends to one
-- statement:
--   Let $k(N)$ be integers with $1\le k(N)\le N$ eventually and $k(N)/\sqrt N\to0$. For optimal conclusive qubit MPBT with fixed maximally entangled resource, define $G(0)=2\int_0^\infty x^2 e^{-x^2/2}/\sqrt{2\pi}\,dx$. Then
--
--   $$p_{\rm succ}(N,k(N))\longrightarrow G(0),\qquad G(0)=1.$$
--
--   Both convergence and the Gaussian second-moment normalization are asserted. The numbered statement uses $N\to\infty$; the preceding prose's $N\to0$ is a typographical error.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 16, Corollary 20 / Eq.(77): subcritical success tends to one

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.16, Corollary 20, Eq.(77): convergence AND the integral normalization.
The preceding prose's N→0 is corrected to infinity as in the numbered statement. -/
theorem subcritical_success (k : ℕ → ℕ)
    (hphysical : ∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N)
    (hscale : Tendsto (fun N => (k N : ℝ) / Real.sqrt N) atTop (nhds 0)) :
    Tendsto (fun N => mpbtSuccessProbability 2 N (k N)) atTop (nhds (gaussianLimit 0)) ∧
    gaussianLimit 0 = 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
