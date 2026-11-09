-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_6_5
-- name    : ResultantVNP.lemma_2_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:25.300291+00:00
-- url     : https://prove2.me/theorems/06f12a95-f345-4579-b253-d1c4562ec62d
-- title:
--   Lemma 2.6(5) — padding with squares
-- statement:
--   Let $1\le k\le n$ and let $f_1,\dots,f_k$ be quadratic forms in $x_1,\dots,x_k$. Viewing them as forms in $x_1,\dots,x_n$,
--
--   $$
--   \mathrm{Res}^{(2)}_n\big(f_1,\dots,f_k,x_{k+1}^2,\dots,x_n^2\big)=\mathrm{Res}^{(2)}_k(f_1,\dots,f_k)^{2^{n-k}} .
--   $$
--
--   The padding variables come last, as fixed by Remark 2.4.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: n ≥ k (k implicit) → 1 ≤ k ≤ n; reason: Res^{(2)}_k exists only for k ≥ 1; nondegeneracy condition excluding the undefined case
--   - encoding: quadratic forms in x₁, …, x_k viewed among x₁, …, xₙ → rename along Fin.castLE (x_j ↦ x_j); reason: Lean convention; same instances
--   - encoding: Res(f₁, …, fₙ) of homogeneous forms → resOf 𝓡 d f: Res_d evaluated at the coefficients [x^e] f_i, |e| = d_i, with each f_i assumed homogeneous of degree d_i; reason: the notation of Definition 2.1 (evaluation at the coefficients of the forms)
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.6(5), p.13

import Mathlib
import Definitions.Def_ResultantVNP_resOf

namespace ResultantVNP

/-- **Lemma 2.6(5) (Padding).** If `f₁, …, f_k` are quadratic forms in `x₁, …, x_k` and `n ≥ k`, then
`Res^{(2)}_n(f₁, …, f_k, x_{k+1}², …, x_n²) = Res^{(2)}_k(f₁, …, f_k)^{2^{n−k}}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.6(5), p.13.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `f_i` is viewed in `n` variables through `x_j ↦ x_j` (`Fin.castLE`); the padding variables
`x_{k+1}, …, x_n` come last (Remark 2.4). `k ≥ 1` (the resultant needs at least one variable). -/
theorem lemma_2_6_5 (𝓡 : ResultantSystem) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (f : Fin k → MvPolynomial (Fin k) ℂ) (hf : ∀ i, (f i).IsHomogeneous 2) :
    resOf 𝓡 (fun _ : Fin n => 2)
        (fun i => if h : (i : ℕ) < k then MvPolynomial.rename (Fin.castLE hkn) (f ⟨i, h⟩)
          else MvPolynomial.X i ^ 2) =
      resOf 𝓡 (fun _ : Fin k => 2) f ^ (2 ^ (n - k)) := by sorry

end ResultantVNP
