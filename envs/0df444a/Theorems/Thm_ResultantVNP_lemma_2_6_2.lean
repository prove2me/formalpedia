-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_6_2
-- name    : ResultantVNP.lemma_2_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:03.068289+00:00
-- url     : https://prove2.me/theorems/71e1c544-ece7-40fb-bfec-fab6d2157044
-- title:
--   Lemma 2.6(2) — resultant of linear forms is the determinant
-- statement:
--   For every $n\ge1$ and every complex $n\times n$ matrix $A=(a_{ij})$,
--
--   $$
--   \mathrm{Res}_{1,\dots,1}\Big(\sum_{j=1}^n a_{1j}x_j,\dots,\sum_{j=1}^n a_{nj}x_j\Big)=\det A .
--   $$
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: Res(f₁, …, fₙ) of homogeneous forms → resOf 𝓡 d f: Res_d evaluated at the coefficients [x^e] f_i, |e| = d_i, with each f_i assumed homogeneous of degree d_i; reason: the notation of Definition 2.1 (evaluation at the coefficients of the forms)
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.6(2), p.12

import Mathlib
import Definitions.Def_ResultantVNP_resOf

namespace ResultantVNP

/-- **Lemma 2.6(2) (Linear case).** The resultant of linear forms is the determinant of their
coefficient matrix: for every `n × n` matrix `A = (a_{ij})`,
`Res_{1,…,1}(∑_j a_{1j} x_j, …, ∑_j a_{nj} x_j) = det A`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.6(2), p.12.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `n ≥ 1`. -/
theorem lemma_2_6_2 (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    resOf 𝓡 (fun _ => 1) (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) = A.det := by sorry

end ResultantVNP
