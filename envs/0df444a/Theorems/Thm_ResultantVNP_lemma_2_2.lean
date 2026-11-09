-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_2
-- name    : ResultantVNP.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:52.562621+00:00
-- url     : https://prove2.me/theorems/dfdfceb9-77ef-47d8-bb5f-59f7f2d2bb15
-- title:
--   Lemma 2.2 — degree of the multivariate resultant
-- statement:
--   Let $n\ge1$ and $d_1,\dots,d_n\ge1$, and put $D_i=\prod_{j\ne i}d_j$. Then:
--
--   1. for each $i$, $\mathrm{Res}_{d_1,\dots,d_n}$ is homogeneous of degree $D_i$ in the block of variables $u_{i,e}$, $|e|=d_i$;
--   2. consequently, for every $\lambda\in\mathbb C$,
--   $$
--   \mathrm{Res}(f_1,\dots,\lambda f_i,\dots,f_n)=\lambda^{D_i}\,\mathrm{Res}(f_1,\dots,f_n);
--   $$
--   3. $\mathrm{Res}_{d_1,\dots,d_n}$ is homogeneous of total degree $\sum_{i=1}^n D_i$;
--   4. in particular $\mathrm{Res}^{(2)}_n$ is homogeneous of total degree $n2^{n-1}$.
--
--   These degree counts give the degree $n2^{n-1}$ of the tensor determinant (Lemma 2.8) and the multihomogeneity used in Theorem 3.5.
--
--   **Formalization Note** Clause 2 is stated for every complex coefficient vector $c$, with the $i$-th block multiplied by $\lambda$ (the forms with coefficients $c$).
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1 and positive degrees d_i; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: homogeneous in the variables u_{i,e}, |e| = d_i, of degree D_i → IsWeightedHomogeneous with weight 1 on the block i and 0 elsewhere; reason: the same notion
--   - encoding: Res(f₁, …, λf_i, …, fₙ) for forms f → evaluation at a coefficient vector c with the i-th block scaled by λ; reason: forms with coefficients c_{i,e} are exactly coefficient vectors
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.2, pp.11–12

import Mathlib
import Definitions.Def_ResultantVNP_quadRes

namespace ResultantVNP

/-- **Lemma 2.2 (Degree of the multivariate resultant).** Let `n ≥ 1` and `d₁, …, dₙ ≥ 1`. For each
`i`, `Res_{d₁,…,dₙ}` is homogeneous in the block of variables `u_{i,e}`, `|e| = d_i`, of degree
`D_i = ∏_{j≠i} d_j`; hence `Res(f₁, …, λf_i, …, fₙ) = λ^{D_i} Res(f₁, …, fₙ)` for every `λ ∈ ℂ`. The total
degree of `Res_{d₁,…,dₙ}` is `∑_i D_i`, and `Res^{(2)}_n` has total degree `n·2^{n−1}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.2, pp.11–12.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. Homogeneity in the `i`-th block is weighted homogeneity with weight `1` on `u_{i,e}` and `0`
elsewhere; "total degree `D`" is homogeneity of degree `D` (the resultant is homogeneous, p.11). The
scaling identity is stated for every complex coefficient vector `c` (forms `f_i` with coefficients `c`). -/
theorem lemma_2_2 (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) :
    (∀ i : Fin n, MvPolynomial.IsWeightedHomogeneous
        (fun v : CoeffVar d => if v.1 = i then 1 else 0) (𝓡.res d)
        (∏ j ∈ Finset.univ.erase i, d j)) ∧
    (∀ (i : Fin n) (t : ℂ) (c : CoeffVar d → ℂ),
        MvPolynomial.eval (fun v => if v.1 = i then t * c v else c v)
            (MvPolynomial.map (Int.castRingHom ℂ) (𝓡.res d)) =
          t ^ (∏ j ∈ Finset.univ.erase i, d j) *
            MvPolynomial.eval c (MvPolynomial.map (Int.castRingHom ℂ) (𝓡.res d))) ∧
    (𝓡.res d).IsHomogeneous (∑ i, ∏ j ∈ Finset.univ.erase i, d j) ∧
    (quadRes 𝓡 n).IsHomogeneous (n * 2 ^ (n - 1)) := by sorry

end ResultantVNP
