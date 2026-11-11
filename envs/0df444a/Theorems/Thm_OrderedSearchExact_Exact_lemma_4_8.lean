-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_8
-- name    : OrderedSearchExact.Exact.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:58.111198+00:00
-- url     : https://prove2.me/theorems/556e6308-aa3a-4d97-9f08-37643f507e1e
-- title:
--   Lemma 4.8 — quartic endpoint inequality and strict ratio
-- statement:
--   For the half-line quantities $A_r,D_{4,d}$ in (32), there is one real constant $0<d_0<\pi$ such that, for every $d\in[d_0,\pi]$ and every real $x$,
--
--   $$D_{4,d}(x)\le\frac d\pi\sqrt{A_4(x)A_4(x-d)}.$$
--
--   Both factors under the square root are strictly positive, and if $d<\pi$ the ratio $D_{4,d}(x)/\sqrt{A_4(x)A_4(x-d)}$ is strictly less than one. The constant $d_0$ is chosen before both $d$ and $x$. This states the full endpoint inequality, including $d=\pi$ in its non-strict clause.
--
--   Differences from the source:
--   - encoding: the determinant ratio in the quartic endpoint model → D_{4,d}(x) divided by sqrt(A_4(x) A_4(x-d)), with both A factors positive; reason: the model has a_h=A_4/2, so the factor 2 in (28) cancels; positivity prevents totalized division from supplying a spurious strict inequality
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.8, p.19 (PDF p.19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Analysis

namespace OrderedSearchExact.Exact

theorem lemma_4_8 :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ < Real.pi ∧ ∀ d : ℝ, d₀ ≤ d → d ≤ Real.pi →
      ∀ x : ℝ, 0 < endpointA 4 x ∧ 0 < endpointA 4 (x - d) ∧
        endpointD d x ≤ (d / Real.pi) * Real.sqrt (endpointA 4 x * endpointA 4 (x - d)) ∧
        (d < Real.pi → endpointRatio d x < 1) := by sorry

end OrderedSearchExact.Exact
