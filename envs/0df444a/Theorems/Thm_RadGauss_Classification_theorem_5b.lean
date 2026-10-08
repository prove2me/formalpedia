-- Prove2me | Theorems.Thm_RadGauss_Classification_theorem_5b
-- name    : RadGauss.Classification.theorem_5b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:46:33.597379+00:00
-- url     : https://prove2.me/theorems/69bf1fc0-a7bb-4f89-b56e-d0a6943aa5f7
-- title:
--   Theorem 5(b) — w.p. ≥ 1 − δ, every ±1 classifier f in F has P(Y ≠ f(X)) ≤ P̂_n(Y ≠ f(X)) + R_n(F)/2 + √(ln(1/δ)/(2n))
-- statement:
--   Let $P$ be a probability distribution on $\mathcal X \times \{\pm1\}$, let $F$ be a set of (measurable) $\{\pm1\}$-valued functions defined on $\mathcal X$, and let $(X_i, Y_i)_{i=1}^n$, $n \ge 1$, be training samples drawn according to $P^n$. Write $\hat P_n(Y \ne f(X)) = \frac1n\#\{i : Y_i \ne f(X_i)\}$ for the training error of $f$, and $R_n(F) = \mathbb E\sup_{f\in F}\big|\frac2n\sum_{i=1}^n\sigma_i f(X_i)\big|$ for the Rademacher complexity (Definition 2) of $F$, viewed as a class of real functions, with respect to the marginal of $P$ on $\mathcal X$. Then for every $0 < \delta < 1$, with probability at least $1 - \delta$, every function $f$ in $F$ satisfies
--
--   $$P(Y \ne f(X)) \le \hat P_n(Y \ne f(X)) + \frac{R_n(F)}{2} + \sqrt{\frac{\ln(1/\delta)}{2n}} .$$
--
--   The bound is uniform: the probability that some $f \in F$ violates it is at most $\delta$. It is a data-dependent alternative to the VC bound for classification, with the class's complexity measured by its Rademacher complexity rather than its VC dimension.
--
--   **Formalization Note** Values are compared in $[0, \infty]$, so an infinite $R_n(F)$ makes the bound trivially true, as in the paper. The bad event is a union over $F$ and is measured by the outer measure of $P^n$. Added hypotheses, all disclosed: $n \ge 1$ (at $n = 0$ the Lean statement would be false, since $2/0 = 0$); $0 < \delta < 1$; measurability of the members of $F$; and measurability of the three random variables the proof integrates — $S \mapsto \sup_f(P(Y\ne f(X)) - \hat P_n(Y\ne f(X)))$, the double-sample supremum $(S,S') \mapsto \sup_f (\hat P'_n - \hat P_n)(Y \ne f(X))$, and $x \mapsto \hat R_n(F)(x)$ on $\mathcal X^n$. Labels are $\mathbb Z^\times = \{1,-1\}$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 465 (PDF p. 3), Theorem 5 (b)

import Mathlib
import Definitions.Def_RadGauss_Classification_Complexity
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

namespace RadGauss.Classification

/-- **Theorem 5 (b)** (Bartlett–Mendelson 2002, p. 465). Let `P` be a probability distribution
on `X × {±1}`, `F` a set of `{±1}`-valued (measurable) functions on `X`, and
`(X_i, Y_i)_{i=1}^n ∼ P^n`. With probability at least `1 − δ`, every `f ∈ F` satisfies
`P(Y ≠ f(X)) ≤ P̂_n(Y ≠ f(X)) + R_n(F)/2 + √(ln(1/δ)/(2n))`,
where `R_n(F)` is the Rademacher complexity (Definition 2) of `F` as a class of real functions,
with respect to the marginal of `P` on `X`. The bad event (some `f ∈ F` violates the bound) has
`P^n`-(outer) measure at most `δ`. Added hypotheses: `0 < n`, `0 < δ < 1`, and the measurability
of the three random variables the proof integrates (`gapSup`, `ghostGapSup`, `R̂_n(F)`). -/
theorem theorem_5b {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ))
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S))
    (hghost : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      ghostGapSup F p.1 p.2))
    (hrad : Measurable (fun x : Fin n → X => empiricalRademacher (realClass F) n x)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (classError P f) ≤ ENNReal.ofReal (trainError S f)
            + rademacherComplexity (P.map Prod.fst) n (realClass F) / 2
            + ENNReal.ofReal (Real.sqrt (Real.log (1 / δ) / (2 * n))))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.Classification
