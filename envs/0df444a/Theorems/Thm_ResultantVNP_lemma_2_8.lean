-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_8
-- name    : ResultantVNP.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:51.163166+00:00
-- url     : https://prove2.me/theorems/74b96eee-6bd0-4828-934c-4aaf31cf3422
-- title:
--   Lemma 2.8 — degree, symmetry and scaling of $\mathrm{Det}_n$
-- statement:
--   Let $n\ge1$, $q=2^{n-1}$ and $D=nq$. For the generic cubic tensor $A=(a_{ijk})$ of dimension $n$:
--
--   1. $\mathrm{Det}_n$ is homogeneous of degree $D$ in the entries $a_{ijk}$;
--   2. for every $\pi\in S_n$ the substitution $a_{ijk}\mapsto a_{\pi(i)\pi(j)\pi(k)}$ leaves $\mathrm{Det}_n$ unchanged;
--   3. for arbitrary scalars $\lambda_1,\dots,\lambda_n$ and every complex tensor $A$,
--   $$
--   \mathrm{Det}_n\big((\lambda_i\lambda_j\lambda_k a_{ijk})_{ijk}\big)=\Big(\prod_{i=1}^n\lambda_i^{3q}\Big)\mathrm{Det}_n(A).
--   $$
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: the substitution a_{ijk} ↦ a_{π(i)π(j)π(k)} leaves Det_n unchanged → rename along (i, j, k) ↦ (π i, π j, π k) fixes tensorDet; reason: the same substitution
--   - encoding: scaling identity (2) for scalars λ_i → identity of evaluations at every complex tensor A and every λ ∈ ℂⁿ; reason: Section 2.3 tensors have complex entries; same instances
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.8, Eq. (2), p.13

import Mathlib
import Definitions.Def_ResultantVNP_tensorDet

namespace ResultantVNP

/-- **Lemma 2.8 (Degree, symmetry, and scaling).** Let `A` be a cubic tensor of dimension `n`, and let
`q = 2^{n−1}` and `D = nq`. The polynomial `Det_n` is homogeneous of degree `D` and invariant under
simultaneous permutation of its three index ranges: for every `π ∈ S_n`, the substitution
`a_{ijk} ↦ a_{π(i)π(j)π(k)}` leaves `Det_n` unchanged. For arbitrary scalars `λ₁, …, λₙ`,
`Det_n((λ_iλ_jλ_k a_{ijk})_{ijk}) = (∏_i λ_i^{3q}) Det_n(A)`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.8, Eq. (2), p.13.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `Det_n` is the polynomial in the `n³` entries of the generic (not necessarily symmetric) tensor;
`n ≥ 1`. The scaling identity is stated at every complex tensor `A` and scalars `λ`. -/
theorem lemma_2_8 (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) :
    (tensorDet 𝓡 n).IsHomogeneous (n * 2 ^ (n - 1)) ∧
    (∀ π : Equiv.Perm (Fin n),
        MvPolynomial.rename (fun t : Fin n × Fin n × Fin n => (π t.1, π t.2.1, π t.2.2))
          (tensorDet 𝓡 n) = tensorDet 𝓡 n) ∧
    (∀ (l : Fin n → ℂ) (A : Fin n × Fin n × Fin n → ℂ),
        MvPolynomial.eval (fun t => l t.1 * l t.2.1 * l t.2.2 * A t)
            (MvPolynomial.map (Int.castRingHom ℂ) (tensorDet 𝓡 n)) =
          (∏ i, l i ^ (3 * 2 ^ (n - 1))) *
            MvPolynomial.eval A (MvPolynomial.map (Int.castRingHom ℂ) (tensorDet 𝓡 n))) := by sorry

end ResultantVNP
