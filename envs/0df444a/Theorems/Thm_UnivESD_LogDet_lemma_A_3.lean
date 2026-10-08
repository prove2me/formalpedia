-- Prove2me | Theorems.Thm_UnivESD_LogDet_lemma_A_3
-- name    : UnivESD.LogDet.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:18.205322+00:00
-- url     : https://prove2.me/theorems/966e8b22-5d23-45b2-a22f-e2372552e026
-- title:
--   Lemma A.3, p. 2058 — Weyl comparison inequality for products of eigenvalues and singular values
-- statement:
--   Let $A\in M_n(\mathbb C)$ have generalized eigenvalues $\lambda_1,\dots,\lambda_n\in\mathbb C$ (eigenvalues counted with algebraic multiplicity), ordered so that $|\lambda_1|\ge\dots\ge|\lambda_n|$, and singular values $\sigma_1(A)\ge\dots\ge\sigma_n(A)\ge0$. Then
--   $$\prod_{j=1}^J|\lambda_j|\le\prod_{j=1}^J\sigma_j(A)\quad(0\le J\le n),\qquad \prod_{j=J}^n\sigma_j(A)\le\prod_{j=J}^n|\lambda_j|\quad(1\le J\le n).$$
--
--   This is the deterministic link between eigenvalues and singular values used on p. 2057 to transfer a bound on the smallest singular values to the eigenvalues of smallest modulus.
--
--   **Formalization Note** The eigenvalues are an enumeration `lam : Fin n → ℂ` whose image multiset is the root multiset of the characteristic polynomial; the paper's $\lambda_j$ is `lam ⟨j-1, _⟩`. The second inequality is stated for $1\le J\le n$: at $J=0$ the printed product contains the undefined $\sigma_0(A)$. The page prints the ordering $|\lambda_1|\le\dots\le|\lambda_n|$; this is a slip. With that ordering both inequalities are strictly weaker than Weyl's inequalities and cannot give their use on p. 2057, where the eigenvalues are ordered $|\lambda_1|\ge\dots\ge|\lambda_n|$ and Lemma A.3 bounds the product of the smallest moduli. The decreasing order is stated here, and it implies the printed form.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2058 (PDF 36), Lemma A.3

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic

namespace UnivESD.LogDet

/-- Lemma A.3 (Weyl comparison inequality for products), Tao–Vu, Ann. Probab. 38 (2010), p. 2058.
`lam : Fin n → ℂ` enumerates the generalized eigenvalues of `A` (the roots of the characteristic
polynomial, with multiplicity), ordered so that `|λ_1| ≥ ⋯ ≥ |λ_n|`; the paper's `λ_j` is
`lam ⟨j - 1, _⟩`, so `{1 ≤ j ≤ J}` is `{j : Fin n | j.val < J}` and `{J ≤ j ≤ n}` is
`{j : Fin n | J ≤ j.val + 1}`. `sv A j` is the one-based `σ_j(A)`.

Formalization Note: the page prints the ordering `|λ_1| ≤ ⋯ ≤ |λ_n|`, a slip: with it both
inequalities are weaker than Weyl's and cannot give the use on p. 2057, where the eigenvalues are
ordered `|λ_1| ≥ ⋯ ≥ |λ_n|` and Lemma A.3 bounds the product of the smallest moduli. The decreasing
order is stated here; it implies the printed form. The second inequality is stated for
`1 ≤ J ≤ n`; at `J = 0` the printed product contains the undefined `σ_0(A)`. -/
theorem lemma_A_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ)
    (hlam : Multiset.map lam Finset.univ.val = A.charpoly.roots)
    (hord : Antitone (fun j => ‖lam j‖)) :
    (∀ J : ℕ, J ≤ n →
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < J), ‖lam j‖ ≤
        ∏ j ∈ Finset.Icc 1 J, sv A j) ∧
    (∀ J : ℕ, 1 ≤ J → J ≤ n →
      ∏ j ∈ Finset.Icc J n, sv A j ≤
        ∏ j ∈ Finset.univ.filter (fun j : Fin n => J ≤ j.val + 1), ‖lam j‖) := by sorry

end UnivESD.LogDet
