-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq54
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq54
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:50:51.977962+00:00
-- url     : https://prove2.me/theorems/ff7d9577-7483-48b4-a1c3-2723424e04ad
-- title:
--   eq54
-- statement:
--   Let $p,q$ be normalized classical probability laws on $d\ge2$ symbols, $a=|S(p)-S(q)|$, and $L=\log^2(d-1)+4$, using natural logarithms. Define the Chernoff information by $\xi(p,q)=-\log\inf_{0<s<1}\sum_i p_i^s q_i^{1-s}$, including one-sided endpoint limits and $-\log0=+\infty$. Then
--
--   $$\xi(p,q)\ge\frac{a^2}{2L}-\frac{a^3}{3L^2}.$$
--
--   If Conjecture 12 holds in this dimension, then also $\xi(p,q)\ge M(-a/2,d)$. Zero masses and disjoint supports are included without assuming a finite common-divergence Hellinger witness. This is the classical commuting entropy-difference bound, not a claim for noncommuting quantum states.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 16, eq54

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eq. (54), PDF p.16: classical commuting states only, including singular endpoints.
No finite common-divergence Hellinger witness is assumed. -/
theorem eq54 {d : ℕ} (hd : 2 ≤ d) (p q : Fin d → ℝ) (hp : isLaw p) (hq : isLaw q) :
    (redundancyBound d |shannonEntropyNats p - shannonEntropyNats q| : EReal) ≤ chernoff p q ∧
    (asymmetryConjecture d →
      tightBound d (-|shannonEntropyNats p - shannonEntropyNats q| / 2) ≤ chernoff p q) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
