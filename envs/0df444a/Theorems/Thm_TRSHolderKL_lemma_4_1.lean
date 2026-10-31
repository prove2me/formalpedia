-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_4_1
-- name    : TRSHolderKL.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:43.519165+00:00
-- url     : https://prove2.me/theorems/87bc8927-1cc8-483c-8c62-576f89e9cd6d
-- title:
--   Lemma 4.1 — a global Hölderian error bound gives the KL inequality for convex functions (Bolte et al., Cor. 6 (ii))
-- statement:
--   Let $H$ be a real Hilbert space and
--   $$
--   \mathcal K(0,+\infty)=\{\varphi\in C^0[0,+\infty)\cap C^1(0,+\infty):\ \varphi(0)=0,\ \varphi\text{ concave},\ \varphi'>0\}.
--   $$
--   Let $h:H\to(-\infty,+\infty]$ be proper, convex and lower semicontinuous with $\min h=0$, let $\varphi\in\mathcal K(0,+\infty)$ and $c>0$, and let $S=\{x\in H: h(x)=\min h\}$. If $s\varphi'(s)\ge c\,\varphi(s)$ for all $s>0$, and $\varphi(h(x))\ge\operatorname{dist}(x,S)$ for all $x$ with $h(x)>0$, then
--   $$
--   \varphi'(h(x))\,\operatorname{dist}(0,\partial h(x))\ge c\qquad\text{for all }x\text{ with }h(x)>0 .
--   $$
--
--   This is the bridge from error bounds (Section 3) to KL inequalities (Section 4) in the convex case.
--
--   **Formalization Note** $h$ takes values in `EReal`; proper, convex and lower semicontinuous is the published `GammaZero`, $\min h=0$ is the published `MinIsZero`, $S$ is `argminSet`, and $\partial h$ is the published convex subdifferential `subgrad`.
--
--   Differences from the source:
--   - encoding: h : H → (−∞, +∞]; S = {x | h(x) = min h} → h : H → EReal with GammaZero h (never −∞, not identically +∞, convex, lsc) and MinIsZero h; S = argminSet h; reason: the same functions and the same set (min h = 0 is attained)
--   - encoding: φ ∈ 𝒦(0, +∞) and φ′ → φ : ℝ → ℝ with IsKZeroInf φ; φ′ is deriv φ; reason: only the values of φ on [0, +∞) matter; on (0, +∞) φ is C¹, so deriv is its derivative
--   - encoding: φ′(h(x)) dist(0, ∂h(x)) ≥ c for all x with h(x) > 0 → ∀ v ∈ ∂h(x), c ≤ φ′(h(x)) ‖v‖, for x with 0 < h(x) < +∞; reason: dist(0, ∂h(x)) is the infimum of ‖v‖ over ∂h(x); at h(x) = +∞, ∂h(x) = ∅ and dist(0, ∅) = +∞, so the conclusion is trivial there
--   - encoding: the hypothesis φ(h(x)) ≥ dist(x, S) for all x with h(x) > 0 → the same for x with 0 < h(x) < +∞; reason: φ is defined on [0, +∞) only, so the hypothesis has content only where h(x) is finite (at h(x) = +∞ it holds with φ(+∞) = +∞)
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 4.1, p.14 (Corollary 6 (ii) of Bolte, Nguyen, Peypouquet and Suter, Math. Program. 2017)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_KLEB_Setting
import Definitions.Def_TRSHolderKL_IsKZeroInf

open MoreauProx.Characterization ErrBoundCplx.KLEB

namespace TRSHolderKL

/-- Lemma 4.1, Jiang and Li, arXiv:1911.11955v2, p.14 (Corollary 6 (ii) of Bolte et al.).
Let `H` be a real Hilbert space and `h : H → (−∞, +∞]` proper, convex and lower
semicontinuous with `min h = 0`; let `φ ∈ 𝒦(0, +∞)`, `c > 0` and `S = {x | h(x) = min h}`.
If `sφ′(s) ≥ cφ(s)` for all `s > 0` and `φ(h(x)) ≥ dist(x, S)` for all `x` with `h(x) > 0`,
then `φ′(h(x)) dist(0, ∂h(x)) ≥ c` for all `x` with `h(x) > 0`.

**Formalization Note.** `h : H → EReal`; proper, convex and lsc is `GammaZero h`, `min h = 0`
is `MinIsZero h`, `S` is `argminSet h`, `∂h` is `subgrad h`. The conclusion
`φ′(h(x)) dist(0, ∂h(x)) ≥ c` is written `∀ v ∈ ∂h(x), c ≤ φ′(h(x)) ‖v‖` on
`0 < h(x) < +∞`; at `h(x) = +∞` the paper's sides involve `φ(+∞)` and `∂h(x) = ∅`
(`dist(0, ∅) = +∞`), and the hypothesis and the conclusion are both restricted to finite
`h(x)`. -/
theorem lemma_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → EReal) (hh : GammaZero h) (hmin : MinIsZero h)
    (φ : ℝ → ℝ) (hφ : IsKZeroInf φ) (c : ℝ) (hc : 0 < c)
    (hmod : ∀ s : ℝ, 0 < s → c * φ s ≤ s * deriv φ s)
    (heb : ∀ x : H, 0 < h x → h x < ⊤ → Metric.infDist x (argminSet h) ≤ φ (h x).toReal) :
    ∀ x : H, 0 < h x → h x < ⊤ → ∀ v ∈ subgrad h x, c ≤ deriv φ (h x).toReal * ‖v‖ := by sorry

end TRSHolderKL
