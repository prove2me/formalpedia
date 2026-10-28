-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_small_batch_comparison
-- name    : QAlgorithms.Papers.Independent.Support50.P42.small_batch_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:20:09.737085+00:00
-- url     : https://prove2.me/theorems/e880c259-6998-4478-9c01-4f9472142405
-- title:
--   Small-batch Schmidt projection yields less than Procrustean filtering
-- statement:
--   Let $1\le n<5$ be a batch size and let $p\in(0,1)$ be the common Schmidt bias. Let $Y(n,p)$ be the expected concentrated entropy from Schmidt projection, before any standardization loss. Then
--
--   $$\frac{Y(n,p)}n<2\min(p,1-p).$$
--
--   The right side is the one-pair Procrustean singlet yield. The comparison uses entropy per input pair, as in Figure 1; product endpoints are excluded because both yields vanish there. This pins the source's strict small-batch efficiency comparison.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 9, §III and Figure 1: Procrustean versus small-batch Schmidt yields

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.9 and Figure 1, pp.20--21: entropy yield per input pair, before
standardization. Product endpoints are excluded from strict comparison. -/
theorem small_batch_comparison (n : ℕ) (hn : 1≤n) (hn5 : n<5)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    projectedYield n p/(n : ℝ)<procrusteanYield p := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
