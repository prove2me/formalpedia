-- Prove2me | Theorems.Thm_RadGauss_Classification_symmetrization
-- name    : RadGauss.Classification.symmetrization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:46:38.48052+00:00
-- url     : https://prove2.me/theorems/a95934ea-7799-4ea4-9e5e-ac7bd850dd34
-- title:
--   Appendix B (corrected) — E sup_{h∈L∘F}(Eh − Ê_nh) ≤ R_n(F)/2 for the 0–1 loss
-- statement:
--   Let $P$ be a probability distribution on $\mathcal X \times \{\pm1\}$, $\mu$ its marginal on $\mathcal X$, $F$ a nonempty set of measurable $\{\pm1\}$-valued functions on $\mathcal X$, $n \ge 1$, and $S = ((X_i, Y_i))_{i=1}^n \sim P^n$. With the 0–1 loss $\mathcal L(Y, f(X)) = \mathbf 1(Y \ne f(X))$,
--
--   $$\mathbb E \sup_{h \in \mathcal L \circ F}\big(\mathbb E h - \hat{\mathbb E}_n h\big) = \mathbb E \sup_{f \in F}\big(P(Y \ne f(X)) - \hat P_n(Y \ne f(X))\big) \le \frac{R_n(F)}{2},$$
--
--   where $R_n(F) = \mathbb E \sup_{f \in F}\big|\frac2n \sum_{i=1}^n \sigma_i f(X_i)\big|$ is the Rademacher complexity (Definition 2) of $F$, viewed as a class of real functions with values in $\{-1, 1\}$, with respect to $\mu$.
--
--   This is the symmetrization half of the proof of Theorem 5(b): the expected worst-case gap between misclassification probability and training error is controlled by the Rademacher complexity of the classifiers themselves, not of the loss class.
--
--   **Formalization Note** The paper prints the chain ending "$= \mathbb E \sup_{f\in F} \frac1n\sum_i \sigma_i f(X_i) = R_n(F)/2$". The last step is only an inequality: $R_n$ has an absolute value inside the supremum, and for a single function $F = \{f\}$ the left side of that step is $0$ while $R_n(F)/2 = \mathbb E\big|\frac1n\sum_i\sigma_i f(X_i)\big| > 0$. The statement here is the chain's conclusion with $\le$, which is what Theorem 5(b) uses. The left side is a real number converted to $[0,\infty]$; it is nonnegative for nonempty $F$. Three random variables are assumed measurable, because the proof integrates them: $S \mapsto \sup_f (P(Y\ne f(X)) - \hat P_n(Y \ne f(X)))$, the double-sample supremum $(S, S') \mapsto \sup_f(\hat P'_n - \hat P_n)(Y \ne f(X))$, and $x \mapsto \hat R_n(F)(x)$. The hypothesis $n \ge 1$ is needed: at $n = 0$ the factor $2/n$ is $0$ in Lean, so $R_0(F) = 0$ while the left side can be positive.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 480 (PDF p. 18), Appendix B (Proof of Theorem 5), third display (last equality corrected to ≤)

import Mathlib
import Definitions.Def_RadGauss_Classification_Complexity
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

namespace RadGauss.Classification

/-- **Symmetrization for the 0–1 loss** (Bartlett–Mendelson 2002, Appendix B, p. 480, third
display, corrected): `E sup_{h ∈ L∘F} (E h − Ê_n h) ≤ R_n(F)/2`, where `L(Y, f(X)) = 1(Y ≠ f(X))`
and `R_n(F)` is the Rademacher complexity (Definition 2, with the absolute value) of the real
class `F ⊆ {±1}^X` with respect to the marginal of `P` on `X`. The paper prints the last step of
its chain as an equality; it is only an inequality (for `F = {f}` the left side of that step is
`0` while `R_n(F)/2 > 0`), and the chain's conclusion is stated with `≤`.
Measurability guards: `S ↦ sup_f (P(Y ≠ f(X)) − P̂_n(Y ≠ f(X)))`, the double-sample supremum
`(S, S') ↦ sup_f (P̂'_n − P̂_n)(Y ≠ f(X))`, and `x ↦ R̂_n(F)(x)` are measurable. -/
theorem symmetrization {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty)
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S))
    (hghost : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      ghostGapSup F p.1 p.2))
    (hrad : Measurable (fun x : Fin n → X => empiricalRademacher (realClass F) n x)) :
    ENNReal.ofReal (∫ S, gapSup P F S ∂(Measure.pi fun _ : Fin n => P))
      ≤ rademacherComplexity (P.map Prod.fst) n (realClass F) / 2 := by sorry

end RadGauss.Classification
