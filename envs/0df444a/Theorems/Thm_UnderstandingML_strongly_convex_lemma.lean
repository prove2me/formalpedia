-- Prove2me | Theorems.Thm_UnderstandingML_strongly_convex_lemma
-- name    : UnderstandingML.strongly_convex_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:16:04.899112+00:00
-- url     : https://prove2.me/theorems/6eef56cb-99e7-4363-84b1-7fa9b7e64de1
-- title:
--   Lemma 13.5: λ‖w‖² is 2λ-strongly convex; strongly convex + convex is strongly convex; a minimizer u of a λ-strongly convex f has f(w) − f(u) ≥ (λ/2)‖w − u‖²
-- statement:
--   **Lemma 13.5.** (1) The function $f(w) = \lambda\|w\|^2$ is $2\lambda$-strongly convex. (2) If $f$ is $\lambda$-strongly convex and $g$ is convex, then $f + g$ is $\lambda$-strongly convex. (3) If $f$ is $\lambda$-strongly convex and $u$ is a minimizer of $f$, then for any $w$, $f(w) - f(u) \ge \frac\lambda2\|w - u\|^2$.
--
--   Formally: with Mathlib's `StrongConvexOn Set.univ`, for every real $\lambda$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.3 p. 175, Lemma 13.5 with its proof

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 13.5** (p. 175). (1) The function `f(w) = λ‖w‖²` is `2λ`-strongly convex. (2) If `f` is
`λ`-strongly convex and `g` is convex, then `f + g` is `λ`-strongly convex. (3) If `f` is
`λ`-strongly convex and `u` is a minimizer of `f`, then for any `w`,
`f(w) − f(u) ≥ (λ/2)‖w − u‖²`. Strong convexity is Mathlib's `StrongConvexOn` (Definition
13.4). -/
theorem strongly_convex_lemma {d : ℕ} :
    (∀ lam : ℝ, StrongConvexOn Set.univ (2 * lam) (fun w : Vec d ↦ lam * ‖w‖ ^ 2)) ∧
    (∀ (lam : ℝ) (f g : Vec d → ℝ), StrongConvexOn Set.univ lam f → ConvexOn ℝ Set.univ g →
      StrongConvexOn Set.univ lam (f + g)) ∧
    ∀ (lam : ℝ) (f : Vec d → ℝ) (u : Vec d), StrongConvexOn Set.univ lam f →
      (∀ w, f u ≤ f w) → ∀ w, lam / 2 * ‖w - u‖ ^ 2 ≤ f w - f u := by sorry

end UnderstandingML
