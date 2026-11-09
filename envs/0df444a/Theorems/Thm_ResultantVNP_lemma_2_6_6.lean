-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_6_6
-- name    : ResultantVNP.lemma_2_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:18.99655+00:00
-- url     : https://prove2.me/theorems/88662890-21be-4a8f-954f-60423664bc89
-- title:
--   Lemma 2.6(6) — evaluation formula
-- statement:
--   Let $n\ge1$, let $h(x,z)$ be a homogeneous form of positive degree $e$ in the $n+1$ variables $(x_1,\dots,x_n,z)$, and let $c_1,\dots,c_n\in\mathbb C$. Then
--
--   $$
--   \mathrm{Res}\big(x_1+c_1z,\dots,x_n+c_nz,\,h\big)=h(-c_1,\dots,-c_n,1),
--   $$
--
--   the resultant having degree vector $(1,\dots,1,e)$ and the variables ordered $(x_1,\dots,x_n,z)$ (Remark 2.4).
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1 and e ≥ 1; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: variables (x₁, …, xₙ, z) → Fin (n + 1) with z = Fin.last n; reason: Remark 2.4's order; Lean convention
--   - encoding: Res(f₁, …, fₙ) of homogeneous forms → resOf 𝓡 d f: Res_d evaluated at the coefficients [x^e] f_i, |e| = d_i, with each f_i assumed homogeneous of degree d_i; reason: the notation of Definition 2.1 (evaluation at the coefficients of the forms)
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.6(6), p.13

import Mathlib
import Definitions.Def_ResultantVNP_resOf

namespace ResultantVNP

/-- **Lemma 2.6(6) (Evaluation).** For a homogeneous form `h(x, z)` of positive degree `e` in the `n + 1`
variables `(x₁, …, xₙ, z)` and constants `c ∈ ℂⁿ`,
`Res(x₁ + c₁z, …, xₙ + cₙz, h) = h(−c₁, …, −cₙ, 1)`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.6(6), p.13.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. The variables are ordered `(x₁, …, xₙ, z)` (Remark 2.4): `z` is `Fin.last n`. The degree vector is
`(1, …, 1, e)`. `n ≥ 1`. -/
theorem lemma_2_6_6 (𝓡 : ResultantSystem) (n e : ℕ) (hn : 1 ≤ n) (he : 0 < e) (c : Fin n → ℂ)
    (h : MvPolynomial (Fin (n + 1)) ℂ) (hh : h.IsHomogeneous e) :
    resOf 𝓡 (Fin.lastCases (motive := fun _ => ℕ) e (fun _ => 1))
        (Fin.lastCases (motive := fun _ => MvPolynomial (Fin (n + 1)) ℂ) h
          (fun i => MvPolynomial.X (Fin.castSucc i) + MvPolynomial.C (c i) * MvPolynomial.X (Fin.last n))) =
      MvPolynomial.eval (Fin.lastCases (motive := fun _ => ℂ) 1 (fun i => -c i)) h := by sorry

end ResultantVNP
