-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_empirical_rademacher_massart
-- name    : SPOBounds.Natarajan.empirical_rademacher_massart
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:28:25.94098+00:00
-- url     : https://prove2.me/theorems/aa472ceb-99fd-46d8-863c-22c66b95ac28
-- title:
--   Proof of Theorem 2 (App. B.1) — Massart step: $\hat{\mathfrak R}^n_{\rm SPO}(\mathcal H)\le\omega_S(\mathcal C)\sqrt{2\log|\mathfrak F_{|\mathbb X}|/n}$
-- statement:
--   Let $S\subseteq\mathbb R^d$ be nonempty, compact and convex, let $w^*$ be any optimization oracle for $S$, let $\mathcal C$ be a nonempty bounded set of cost vectors, and let $\mathcal H$ be a family of functions $f:\mathcal X\to\mathbb R^d$. Fix a sample $(x_1,c_1),\dots,(x_n,c_n)$ with $n\ge1$ and every $c_i\in\mathcal C$, and let
--   $$\mathfrak F_{|\mathbb X}=\{(w^*(f(x_1)),\dots,w^*(f(x_n))):f\in\mathcal H\}.$$
--   If $\mathfrak F_{|\mathbb X}$ is finite, then
--   $$\hat{\mathfrak R}^n_{\rm SPO}(\mathcal H)\le\omega_S(\mathcal C)\sqrt{\frac{2\log|\mathfrak F_{|\mathbb X}|}{n}}.$$
--
--   The empirical complexity depends on $f$ only through the decision vector in $\mathfrak F_{|\mathbb X}$, and each SPO loss lies in $[0,\omega_S(\mathcal C)]$; this is the step of the proof of Theorem 2 that the paper attributes to Massart's lemma and the definition of $\omega_S(\mathcal C)$.
--
--   **Formalization Note** The finiteness hypothesis makes explicit what the printed inequality leaves implicit (for infinite $\mathfrak F_{|\mathbb X}$ its right-hand side is $+\infty$); without it Lean's `ncard` would be $0$. For empty $\mathcal H$ both sides are $0$. The logarithm is natural.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 31, Appendix B.1 (proof of Theorem 2), the displayed chain, fourth line

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher
import Definitions.Def_SPOBounds_Natarajan_NatarajanDim

namespace SPOBounds.Natarajan

/-- **Proof of Theorem 2, Massart step** (arXiv:1905.11488v3, Appendix B.1, p. 31, the
displayed chain, fourth line). For a fixed sample `s` whose cost vectors lie in the nonempty
bounded set `C`, if the set `𝔉_{|𝕏}` of decision vectors `(w(f(x₁)), …, w(f(xₙ)))`, `f ∈ H`,
is finite, then `R̂ⁿ_SPO(H) ≤ ω_S(C) √(2 log |𝔉_{|𝕏}| / n)`. -/
theorem empirical_rademacher_massart {d : ℕ} {X : Type*}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (n : ℕ) (hn : 0 < n) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) (hsC : ∀ i, (s i).2 ∈ C)
    (hfin : (sampleDecisions w H s).Finite) :
    empRademacherSPO w H s ≤
      linGapSet S C * Real.sqrt (2 * Real.log ((sampleDecisions w H s).ncard : ℝ) / n) := by sorry

end SPOBounds.Natarajan
