-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_5_15
-- name    : TightQLB.Supplement.theorem_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:26:29.116113+00:00
-- url     : https://prove2.me/theorems/c8fe06c5-c5f0-453b-928c-087bdab7f4f2
-- title:
--   Theorem 5.15 — the projection onto the lower degree: $\Pi^{a+e_i}_{\le r-1}g=(T_ig+rg)/(|a|+2r-1)\in R^{a+e_i}_{r-1}$
-- statement:
--   Let $a=(a_1,\dots,a_N)$ with all $a_i\ge1$ real, let $r\ge1$, let $g\in R^a_r$ (a polynomial in $p$ of degree at most $r$ that is $\mathrm{Dir}(a)$-orthogonal to all polynomials of degree at most $r-1$), and let $i\in[N]$. Then the orthogonal projection of $g$ onto the polynomials of degree at most $r-1$ in $L^2(\mathrm{Dir}(a+e_i))$ is
--
--   $$
--   \Pi^{a+e_i}_{\le r-1}\,g=\frac{T_ig+rg}{|a|+2r-1},
--   $$
--
--   and this polynomial lies in $R^{a+e_i}_{r-1}$. Here $T_ig=\partial_ig-\sum_jp_j\partial_jg$ and $|a|=\sum_ia_i$.
--
--   The identity describes how a polynomial of exact degree $r$ under the prior $\mathrm{Dir}(a)$ splits under the posterior $\mathrm{Dir}(a+e_i)$ obtained by observing the outcome $i$.
--
--   **Formalization Note** The projection identity is stated as: the right-hand side has degree at most $r-1$ and $g$ minus it is $\mathrm{Dir}(a+e_i)$-orthogonal to every polynomial of degree at most $r-1$.
--
--   Differences from the source:
--   - encoding: Π^{a+e_i}_{≤r−1} g = h ∈ R^{a+e_i}_{r−1}, an identity in L²(Dir(a+e_i)) → IsProjLe (a+e_i) (r−1) g h ∧ InR (a+e_i) (r−1) h for every polynomial representative g; reason: h is the orthogonal projection exactly when it lies in the finite-dimensional subspace and g − h is orthogonal to it
--   - encoding: Dir(a), density ∝ Π p_i^{a_i−1} with respect to the uniform measure on the simplex → weight Π p_i^{a_i−1} against the (N−1)-dimensional Hausdorff measure restricted to the simplex, divided by its total weight; reason: the normalization of the uniform measure cancels
--   - generalization: the outcome set [N], N = 2^n ≥ 2 → an arbitrary finite type ι; reason: §5.4 uses only a_i ≥ 1 and never N = 2^n; ι = Qubits n is the source's statement
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 5.15, p. 39 (PDF p. 42)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Dirichlet

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 5.15 (The projection onto the lower degree)**, p.39 (PDF p.42).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let `g ∈ R^a_r` with `r ≥ 1` and let `i ∈ [N]`. Then
`Π^{a+e_i}_{≤r−1} g = (T_i g + r g)/(|a| + 2r − 1) ∈ R^{a+e_i}_{r−1}`." (§5.4: "Throughout this
subsection, `a_i ≥ 1`.")

**Formalization Note.**
* `[N]` is a finite type `ι`; `a_i ≥ 1` are real; `g` is any polynomial representative in `R^a_r`
  (`InR a r g`).
* The equality `Π^{a+e_i}_{≤r−1} g = h` in `L²(Dir(a + e_i))` is `IsProjLe (a + e_i) (r − 1) g h`:
  `h` has degree at most `r − 1` and `g − h` is `Dir(a + e_i)`-orthogonal to all polynomials of
  degree at most `r − 1`. The membership is `InR (a + e_i) (r − 1) h`.
* `h = C((|a| + 2r − 1)⁻¹) · (T_i g + C(r) · g)`, with `T_i` the tangent derivative (42). -/
theorem theorem_5_15 {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i)
    (r : ℕ) (hr : 1 ≤ r) (g : MvPolynomial ι ℂ) (hg : InR a r g) (i : ι) :
    IsProjLe (addE a i) (r - 1) g
        (MvPolynomial.C (((absA a + 2 * r - 1 : ℝ) : ℂ)⁻¹) *
          (tangentDeriv i g + MvPolynomial.C (r : ℂ) * g)) ∧
      InR (addE a i) (r - 1)
        (MvPolynomial.C (((absA a + 2 * r - 1 : ℝ) : ℂ)⁻¹) *
          (tangentDeriv i g + MvPolynomial.C (r : ℂ) * g)) := by sorry

end TightQLB.Supplement
