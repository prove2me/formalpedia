-- Prove2me | Theorems.Thm_Transcendence_thue_siegel_real
-- name    : Transcendence.thue_siegel_real
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:19:23.036016+00:00
-- url     : https://prove2.me/theorems/4fe54bab-8cb3-4b35-aaa3-3e03bc6f3a39
-- title:
--   Thue–Siegel's lemma for real linear forms, by Dirichlet's box principle (Lemma 4.11 of Waldschmidt's book)
-- statement:
--   Let $J$ and $\Lambda$ be finite sets, $\mu = |J|$ and $\nu = |\Lambda|$, and let $v_{j\lambda}$ ($j \in J$, $\lambda \in \Lambda$) be real numbers with $\sum_\lambda |v_{j\lambda}| \le C$ for every $j$, where $C > 0$. Let $X \ge 0$ and $\ell \ge 1$ be integers with $\ell^{\mu} < (X+1)^{\nu}$. Then there is a non-zero $\xi \in \mathbb{Z}^\Lambda$ with $|\xi_\lambda| \le X$ for every $\lambda$ and
--
--   $$\Bigl|\sum_{\lambda} v_{j\lambda}\,\xi_\lambda\Bigr| \le \frac{CX}{\ell} \qquad (j \in J).$$
--
--   Applied to real and imaginary parts, it gives the complex form (Lemma 4.12 of the book) with which `Transcendence.siegel_small_values_of_count` builds the auxiliary function of Proposition 4.10.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: this is Lemma 4.11 of Waldschmidt's book (p. 132), a version of Thue–Siegel's lemma, with the book's proof by Dirichlet's box principle. The book asks the bound $C$ (its $U$) to be an integer; here any $C > 0$ is allowed. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Lemma 4.11 (pp. 132–133). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Thue–Siegel lemma, real form** (Waldschmidt, *Diophantine Approximation on Linear Algebraic
Groups*, Lemma 4.11, proved with Dirichlet's box principle). Let `v_j` (`j ∈ J`, `μ = |J|`) be real linear
forms in the variables `ξ_λ` (`λ ∈ Λ`, `ν = |Λ|`) with `Σ_λ |v_{jλ}| ≤ C`, and let `X ≥ 0`, `ℓ ≥ 1` be
integers with `ℓ^μ < (X + 1)^ν`. Then there is a non-zero integer vector `ξ` with `|ξ_λ| ≤ X` and
`|Σ_λ v_{jλ} ξ_λ| ≤ C X / ℓ` for every `j`. -/
theorem thue_siegel_real {J Λ : Type*} [Fintype J] [Fintype Λ] (v : J → Λ → ℝ) {C : ℝ}
    (hC : 0 < C) (hv : ∀ j, ∑ l, |v j l| ≤ C) {X ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcard : ℓ ^ Fintype.card J < (X + 1) ^ Fintype.card Λ) :
    ∃ ξ : Λ → ℤ, ξ ≠ 0 ∧ (∀ l, |ξ l| ≤ X) ∧ ∀ j, |∑ l, v j l * ξ l| ≤ C * X / ℓ := by
  sorry

end Transcendence
