-- Prove2me | Theorems.Thm_RadGauss_Classification_gapSup_bounded_difference
-- name    : RadGauss.Classification.gapSup_bounded_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:46:01.776131+00:00
-- url     : https://prove2.me/theorems/7df68cde-fde7-42e9-807e-99fad88b140f
-- title:
--   Appendix B — replacing one example changes sup_f (P(Y ≠ f(X)) − P̂_n(Y ≠ f(X))) by at most 1/n
-- statement:
--   Let $P$ be a probability distribution on $\mathcal X \times \{\pm1\}$, $F$ a set of $\{\pm1\}$-valued functions on $\mathcal X$, and $n$ a natural number. For a sample $S = ((X_1, Y_1), \dots, (X_n, Y_n))$ write
--   $$\Phi(S) = \sup_{f \in F}\big(P(Y \ne f(X)) - \hat P_n(Y \ne f(X))\big).$$
--   If $S^{(i)}$ is obtained from $S$ by replacing the $i$-th example $(X_i, Y_i)$ by an arbitrary point $(x', y') \in \mathcal X \times \{\pm 1\}$, then
--
--   $$\big|\Phi(S) - \Phi(S^{(i)})\big| \le \frac1n .$$
--
--   This bounded-difference property is the hypothesis under which McDiarmid's inequality applies to $\Phi$ with constants $c_i = 1/n$.
--
--   **Formalization Note** Replacement is `Function.update S i z'`. Sample indices are $0, \dots, n-1$. For empty $F$ the supremum is $0$ in Lean and the statement holds trivially; for $n = 0$ there is no index and the statement is vacuous.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 480 (PDF p. 18), Appendix B (Proof of Theorem 5), sentence after the first display

import Mathlib
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

namespace RadGauss.Classification

/-- **Bounded differences for the 0–1 loss** (Bartlett–Mendelson 2002, Appendix B, p. 480):
"when `(X_i, Y_i)` changes, the supremum changes by no more than `1/n`". For every sample `S`,
index `i` and replacement point `z'`, replacing the `i`-th example of `S` by `z'` changes
`sup_{f ∈ F} (P(Y ≠ f(X)) − P̂_n(Y ≠ f(X)))` by at most `1/n`. -/
theorem gapSup_bounded_difference {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) {n : ℕ}
    (S : Fin n → X × ℤˣ) (i : Fin n) (z' : X × ℤˣ) :
    |gapSup P F S - gapSup P F (Function.update S i z')| ≤ 1 / (n : ℝ) := by sorry

end RadGauss.Classification
