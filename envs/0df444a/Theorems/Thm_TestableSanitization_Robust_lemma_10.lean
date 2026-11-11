-- Prove2me | Theorems.Thm_TestableSanitization_Robust_lemma_10
-- name    : TestableSanitization.Robust.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:53:29.731283+00:00
-- url     : https://prove2.me/theorems/cf760d68-67ab-4a2e-90a8-a2910f6fd139
-- title:
--   Lemma 10 — if $\phi_{f,L}(x)\le b$ then $\Pr_{W\sim U(B_s)}[f(y+W)\neq f(x)]+e<0.4$ for every $y\in B(x,r)$
-- statement:
--   Let $d\ge1$, $0<r<L$, and let $s$, $b$, $e$ be as in (1):
--   $$s=\sqrt{L^2-r^2+\tfrac{16r^2}d}-\tfrac{4r}{\sqrt d},\qquad b=\tfrac1{32}\Big(\tfrac sL\Big)^d,\qquad 0<e\le\tfrac18.$$
--   Let $f:\mathbb R^d\to\{\pm1\}$ be measurable and $x\in\mathbb R^d$. If $\phi_{f,L}(x)\le b$, then for every $y$ in the closed ball $B(x,r)$,
--   $$\Pr_{W\sim U(B_s)}[f(y+W)\neq f(x)]+e<0.4 .$$
--
--   This is the local-correction step of the sanitizer: a point that passes the test at radius $L$ has, at every point within distance $r$, a radius-$s$ neighbourhood whose majority label is $f(x)$, so correcting by the local majority makes the output constant on $B(x,r)$.
--
--   Differences from the source:
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: L, s, b, e as in (1) (for any L > r, with r > 0 the robustness radius) → hypotheses 0 < r, r < L, 0 < e, e ≤ 1/8, with s = sParam d L r and b = bParam d L r; reason: the definitions of (1)
--   - encoding: a Borel-measurable classifier f : R^d → {±1} (§2 standing assumption) → f : Pt d → ℝ with IsClassifier f (Measurable f and every value is 1 or -1); reason: the two labels ±1 as reals; same functions
--   - encoding: the constant 0.4 and Pr_{W∼U(B_s)}[·] as a real probability → 2/5 and the real value of the ballLaw 0 s measure of {w | f(y + w) ≠ f(x)}; reason: same numbers
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 25 (PDF 27), Lemma 10

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary
import Definitions.Def_TestableSanitization_Robust_Params

open MeasureTheory

namespace TestableSanitization.Robust

theorem lemma_10 (d : ℕ) (hd : 1 ≤ d) (r L e : ℝ) (hr : 0 < r) (hL : r < L) (he : 0 < e)
    (he' : e ≤ 1 / 8) (f : Pt d → ℝ) (hf : IsClassifier f) (x : Pt d)
    (hx : lns f L x ≤ bParam d L r) :
    ∀ y ∈ Metric.closedBall x r,
      (ballLaw 0 (sParam d L r) {w | f (y + w) ≠ f x}).toReal + e < 2 / 5 := by sorry

end TestableSanitization.Robust
