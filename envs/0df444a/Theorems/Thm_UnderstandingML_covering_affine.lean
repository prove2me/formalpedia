-- Prove2me | Theorems.Thm_UnderstandingML_covering_affine
-- name    : UnderstandingML.covering_affine
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:48:57.018126+00:00
-- url     : https://prove2.me/theorems/b3aec287-868e-4491-b61d-cf56fbf6045a
-- title:
--   Lemma 27.2 (as its one-line proof gives it): N(cr, {ca + a₀ : a ∈ A}) ≤ N(r, A) for c > 0, r > 0
-- statement:
--   **Lemma 27.2.** For any $A \subset \mathbb{R}^m$, scalar $c > 0$, and vector $a_0 \in \mathbb{R}^m$, we have $\forall r > 0$, $N(cr, \{ca + a_0 : a \in A\}) \le N(r, A)$: the image of an $r$-cover of $A$ is a $cr$-cover of the image.
--
--   The book prints $N(r, \{ca + a_0 : a \in A\}) \le N(cr, A)$, with the radii exchanged. That is false: for $A = [0, 1] \subset \mathbb{R}$, $c = 10$ and $r = 0.01$ it would say $N(0.01, [0, 10]) = 500 \le 5 = N(0.1, [0, 1])$. The statement here is the one the book calls immediate from the definition.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §27.1.1 p. 388, Lemma 27.2

import Definitions.Def_UnderstandingML_Covering

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 27.2** (p. 388), as "immediate from the definition" gives it. For any `A ⊆ ℝ^m`,
scalar `c > 0`, and vector `a₀ ∈ ℝ^m`, the image of an `r`-cover of `A` under `a ↦ ca + a₀` is a
`cr`-cover of the image, so `∀ r > 0, N(cr, {c a + a₀ : a ∈ A}) ≤ N(r, A)`. The book prints
`N(r, {c a + a₀}) ≤ N(cr, A)`, which is false: for `A = [0, 1] ⊆ ℝ`, `c = 10`, `r = 0.01` it reads
`N(0.01, [0, 10]) = 500 ≤ 5 = N(0.1, [0, 1])`. -/
theorem covering_affine {m : ℕ} (A : Set (Fin m → ℝ)) (c : ℝ) (hc : 0 < c) (a₀ : Fin m → ℝ)
    (r : ℝ) (hr : 0 < r) :
    coveringNumber (c * r) ((fun a ↦ c • a + a₀) '' A) ≤ coveringNumber r A := by sorry

end UnderstandingML
