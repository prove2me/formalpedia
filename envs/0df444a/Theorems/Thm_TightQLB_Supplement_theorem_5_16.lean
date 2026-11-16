-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_5_16
-- name    : TightQLB.Supplement.theorem_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:26:56.796956+00:00
-- url     : https://prove2.me/theorems/9ed076ed-5e12-4b44-b3df-7c8595543ea9
-- title:
--   Theorem 5.16 — average squared norm of the lower-degree projection: $\sum_i\frac{a_i}{|a|}\|\Pi^{a+e_i}_{\le r-1}g\|^2_{a+e_i}=\frac{r}{|a|+2r-1}\|g\|_a^2$
-- statement:
--   Let $a=(a_1,\dots,a_N)$ with all $a_i\ge1$ real, $|a|=\sum_ia_i$. For every $r\ge1$ and every $g\in R^a_r$,
--
--   $$
--   \sum_{i=1}^N\frac{a_i}{|a|}\,\big\|\Pi^{a+e_i}_{\le r-1}g\big\|^2_{a+e_i}=\frac{r}{|a|+2r-1}\,\|g\|_a^2 .
--   $$
--
--   On average over the observed outcome $i$, drawn with probability $a_i/|a|$, a polynomial of exact degree $r$ loses only the fraction $r/(|a|+2r-1)\le r/N$ of its squared norm to the lower degree; this is the central estimate of the query argument.
--
--   Differences from the source:
--   - encoding: ‖Π^{a+e_i}_{≤r−1} g‖_{a+e_i} → projNormLe (a+e_i) (r−1) g, the supremum of |⟨v, g⟩_{a+e_i}| over polynomials v of degree at most r−1 with ‖v‖_{a+e_i} ≤ 1; reason: this is the norm of the orthogonal projection onto that subspace
--   - encoding: Dir(a), density ∝ Π p_i^{a_i−1} with respect to the uniform measure on the simplex → weight Π p_i^{a_i−1} against the (N−1)-dimensional Hausdorff measure restricted to the simplex, divided by its total weight; reason: the normalization of the uniform measure cancels
--   - generalization: the outcome set [N], N = 2^n ≥ 2 → an arbitrary finite type ι; reason: §5.4 uses only a_i ≥ 1 and never N = 2^n; ι = Qubits n is the source's statement
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 5.16, p. 40 (PDF p. 43)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Dirichlet

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 5.16 (Average squared norm of the lower-degree projection)**, p.40 (PDF p.43).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"For every `r ≥ 1` and `g ∈ R^a_r`,
`Σ_{i=1}^N (a_i/|a|) ‖Π^{a+e_i}_{≤r−1} g‖²_{a+e_i} = r/(|a| + 2r − 1) ‖g‖²_a`." (§5.4: "Throughout
this subsection, `a_i ≥ 1`.")

**Formalization Note.** `[N]` is a finite type `ι`; `a_i ≥ 1` are real; `g` is any polynomial
representative in `R^a_r`. `‖Π^{a+e_i}_{≤r−1} g‖_{a+e_i}` is `projNormLe (a + e_i) (r − 1) g`, the norm
of the orthogonal projection of `g` onto the polynomials of degree at most `r − 1` in
`L²(Dir(a + e_i))`; `‖g‖²_a` is `dirNormSq a g`. -/
theorem theorem_5_16 {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i)
    (r : ℕ) (hr : 1 ≤ r) (g : MvPolynomial ι ℂ) (hg : InR a r g) :
    ∑ i, a i / absA a * projNormLe (addE a i) (r - 1) g ^ 2 =
      r / (absA a + 2 * r - 1) * dirNormSq a g := by sorry

end TightQLB.Supplement
