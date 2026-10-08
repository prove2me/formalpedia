-- Prove2me | Theorems.Thm_RadGauss_RiskBound_theorem_8
-- name    : RadGauss.RiskBound.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:22:38.522681+00:00
-- url     : https://prove2.me/theorems/049982c6-8491-4e8d-9106-3d1d2da58467
-- title:
--   Theorem 8 — w.p. $\ge 1-\delta$, $\mathbf E\mathcal L(Y,f(X))\le\hat{\mathbf E}_n\phi(Y,f(X))+R_n(\tilde\phi\circ F)+\sqrt{8\ln(2/\delta)/n}$ for every $f\in F$
-- statement:
--   Let $\mathcal X$ be an input space, $\mathcal A$ an action space containing a distinguished action $0$, and $\mathcal Y$ an output space. Let $\mathcal L : \mathcal Y \times \mathcal A \to [0, 1]$ be a loss function and $\phi : \mathcal Y \times \mathcal A \to [0, 1]$ a **dominating cost function**, $\phi(y, a) \ge \mathcal L(y, a)$ for all $y \in \mathcal Y$, $a \in \mathcal A$. Let $F$ be a class of functions from $\mathcal X$ to $\mathcal A$, and let $(X_1, Y_1), \dots, (X_n, Y_n)$ be independent, each distributed according to a probability measure $P$ on $\mathcal X \times \mathcal Y$; $(X, Y)$ denotes a fresh draw from $P$ and $\hat{\mathbf E}_n h(X, Y) = \frac1n\sum_{i=1}^n h(X_i, Y_i)$. Then for every integer $n \ge 1$ and every $0 < \delta < 1$, with probability at least $1 - \delta$ over samples of length $n$, every $f \in F$ satisfies
--
--   $$\mathbf E\mathcal L(Y, f(X)) \le \hat{\mathbf E}_n\phi(Y, f(X)) + R_n(\tilde\phi\circ F) + \sqrt{\frac{8\ln(2/\delta)}{n}},$$
--
--   where $\tilde\phi\circ F = \{(x, y) \mapsto \phi(y, f(x)) - \phi(y, 0) : f \in F\}$ and $R_n$ is the Rademacher complexity of Definition 2 with respect to $P$.
--
--   The bound controls the expected loss of every predictor in the class, including one chosen after seeing the data, by an observable surrogate cost plus a complexity penalty of the centred cost class; it is the decision-theoretic risk bound of the paper, covering multiclass and other structured prediction problems.
--
--   **Formalization Note**
--   1. The probability is the product measure $P^n$ of the set of samples on which some $f \in F$ violates the bound (an outer measure, so the event need not be measurable); the quantifier over $F$ is inside the event.
--   2. $R_n$ takes values in $[0, \infty]$, so the inequality is stated in $[0,\infty]$, with the real, nonnegative terms $\mathbf E\mathcal L$, $\hat{\mathbf E}_n\phi$ and the square root embedded by `ENNReal.ofReal`.
--   3. Added hypotheses, all implicit in the paper: $n \ge 1$ (at $n = 0$ the bound would read $\mathbf E\mathcal L \le 0$, false); $\mathcal L$, $\phi$ and the members of $F$ are measurable; $\mathcal A$ has a distinguished element $0$.
--   4. Measurability guard: three random variables are assumed measurable — the uniform deviation $S \mapsto \sup_{h\in\tilde\phi\circ F}(\mathbf Eh - \hat{\mathbf E}_nh)$, the empirical Rademacher complexity $S \mapsto \hat R_n(\tilde\phi\circ F)(S)$, and the double-sample deviation $(S, S') \mapsto \sup_h(\frac1n\sum_i h(S'_i) - \hat{\mathbf E}_nh)$. They hold, for instance, for countable $F$. Without them $R_n$ would be a lower integral and the bound could fail.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 467 (PDF p. 5), Theorem 8

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Theorem 8** (p. 467). Let `L : 𝒴 × 𝒜 → [0, 1]` be a loss and `φ : 𝒴 × 𝒜 → [0, 1]` a cost
dominating it, `F` a class of maps `𝒳 → 𝒜`, and `(X_i, Y_i)_{i=1}^n` i.i.d. from the probability
measure `P` on `𝒳 × 𝒴`. For every `n ≥ 1` and `0 < δ < 1`, with probability at least `1 − δ`
every `f ∈ F` satisfies
`E L(Y, f(X)) ≤ Ê_n φ(Y, f(X)) + R_n(φ̃∘F) + √(8 ln(2/δ)/n)`,
where `φ̃∘F = {(x, y) ↦ φ(y, f(x)) − φ(y, 0) : f ∈ F}`. The probability of the bad event is an
outer measure. Measurability guard: the uniform deviation, the empirical Rademacher complexity
of `φ̃∘F` and the double-sample supremum are measurable functions of the sample(s). -/
theorem theorem_8 {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (∫ z, L z.2 (f z.1) ∂P) ≤
          ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1))) +
            rademacherComplexity P n (phiTildeComp φ F) +
            ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.RiskBound
