-- Prove2me | Theorems.Thm_TestableSanitization_Robust_eq_8
-- name    : TestableSanitization.Robust.eq_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:53:56.820223+00:00
-- url     : https://prove2.me/theorems/4847591e-a5bc-4c0c-a56a-7ac0b1dc255c
-- title:
--   §4.1, Eq. (8) — with $L=\alpha r$ and $s$ from (1): $(L/s)^d\le e^{32}\,(1+\tfrac1{\alpha^2-1})^d$
-- statement:
--   Let $d\ge1$, $\alpha>1$, $r>0$, $L=\alpha r$ and $s=\sqrt{L^2-r^2+16r^2/d}-4r/\sqrt d$ as in (1). Then $M=(L/s)^d$ satisfies
--   $$M\le\exp(32)\Big(1+\frac1{\alpha^2-1}\Big)^d .$$
--
--   Since $K=O(M\log(m/\zeta))$, this is where the factor $(1+1/(\alpha^2-1))^d$ in the query complexity of Theorem 1 comes from.
--
--   Differences from the source:
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: M = (L/s)^d with L = αr, s from (1), r > 0 → (α * r / sParam d (α * r) r) ^ d with 0 < r; reason: the definitions of (1)
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 27 (PDF 29), §4.1, proof of Theorem 1, Eq. (8)

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Params

open MeasureTheory

namespace TestableSanitization.Robust

theorem eq_8 (d : ℕ) (hd : 1 ≤ d) (α r : ℝ) (hα : 1 < α) (hr : 0 < r) :
    (α * r / sParam d (α * r) r) ^ d ≤ Real.exp 32 * (1 + 1 / (α ^ 2 - 1)) ^ d := by sorry

end TestableSanitization.Robust
