-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_proposition_3_4
-- name    : ProportionalTSP.Exact.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:17.035218+00:00
-- url     : https://prove2.me/theorems/f5593151-9ba5-4ee6-8cb8-d4c094cb7fcd
-- title:
--   Proposition 3.4 — Exact coefficient count and every-z bound
-- statement:
--   For $1\le k\le m$, the output count and compatible-family cardinality satisfy
--   $$N_{m,k}=2^{k-m}\sum_{j=k}^{2m}[z^j](2+z+z^2)^m,\qquad |\mathcal C(w)|=N_{m,k}.$$
--   For every real $z\ge1$,
--   $$N_{m,k}\le2^{k-m}z^{-k}(2+z+z^2)^m.$$
--   The powers $k-m$ and $-k$ are signed integer powers. Both the exact coefficient identity and the full bound are retained; this is the exponential-count input to the headline theorem.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: signed exponents k-m and -k → integer powers after casting k and m to integers; reason: natural subtraction would truncate the negative exponent and change the formula
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Proposition 3.4, PDF p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem proposition_3_4 {m k : ℕ} [NeZero m] [NeZero k] (hkm : k ≤ m)
    (w : Fin m → Fin k → ℝ) (hw : Generic w) :
    (outputCount m k : ℝ) = (2 : ℝ)^((k : ℤ)-(m : ℤ)) *
      (∑ j ∈ Finset.Icc k (2*m),
        (((Polynomial.C 2 + Polynomial.X + Polynomial.X^2 : Polynomial ℕ)^m).coeff j : ℝ)) ∧
    (compatibleFamily w).card = outputCount m k ∧
    ∀ z : ℝ, 1 ≤ z → (outputCount m k : ℝ) ≤
      (2 : ℝ)^((k : ℤ)-(m : ℤ)) * z^(-(k : ℤ)) * (2+z+z^2)^m := by sorry

end ProportionalTSP.Exact
