-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_6_1
-- name    : ResultantVNP.lemma_2_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:01.790208+00:00
-- url     : https://prove2.me/theorems/acdf7b0e-2400-4372-97cb-4f3beda92ef0
-- title:
--   Lemma 2.6(1) — multiplicativity of the resultant
-- statement:
--   Let $n\ge1$, fix a slot $i$, let $f_j$ ($j\ne i$) be homogeneous forms of degrees $d_j\ge1$ in $n$ variables, and let $g,h$ be homogeneous forms of degrees $a,b\ge1$. Then
--
--   $$
--   \mathrm{Res}(\dots,gh,\dots)=\mathrm{Res}(\dots,g,\dots)\,\mathrm{Res}(\dots,h,\dots),
--   $$
--
--   where $gh,g,h$ occupy slot $i$ and the three resultants have the degree vectors with $d_i$ replaced by $a+b$, $a$, $b$ respectively.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - reading: with the appropriate degrees → degree vectors d with slot i replaced by a + b, a, b; g, h homogeneous of positive degrees a, b; the other forms homogeneous of positive degrees d_j; reason: deg(gh) = deg g + deg h; Definition 2.1 needs positive degrees
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: Res(f₁, …, fₙ) of homogeneous forms → resOf 𝓡 d f: Res_d evaluated at the coefficients [x^e] f_i, |e| = d_i, with each f_i assumed homogeneous of degree d_i; reason: the notation of Definition 2.1 (evaluation at the coefficients of the forms)
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.6(1), p.12

import Mathlib
import Definitions.Def_ResultantVNP_resOf

namespace ResultantVNP

/-- **Lemma 2.6(1) (Multiplicativity).** The normalized resultant is multiplicative in each form:
`Res(…, gh, …) = Res(…, g, …) Res(…, h, …)`, with the appropriate degrees. Here the forms in the
slots `j ≠ i` have degrees `d_j ≥ 1`, and `g, h` (slot `i`) are forms of degrees `a, b ≥ 1`, so `gh` has
degree `a + b`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.6(1), p.12.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `resOf 𝓡 d f` is `Res_{d}(f₁, …, fₙ)`; the degree vector of each resultant is `d` with slot `i`
replaced by `a + b`, `a`, `b` respectively. -/
theorem lemma_2_6_1 (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ) (i : Fin n)
    (hd : ∀ j, j ≠ i → 0 < d j) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ j, j ≠ i → (f j).IsHomogeneous (d j))
    (g h : MvPolynomial (Fin n) ℂ) (hg : g.IsHomogeneous a) (hh : h.IsHomogeneous b) :
    resOf 𝓡 (Function.update d i (a + b)) (Function.update f i (g * h)) =
      resOf 𝓡 (Function.update d i a) (Function.update f i g) *
        resOf 𝓡 (Function.update d i b) (Function.update f i h) := by sorry

end ResultantVNP
