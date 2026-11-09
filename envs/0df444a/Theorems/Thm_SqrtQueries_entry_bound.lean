-- Prove2me | Theorems.Thm_SqrtQueries_entry_bound
-- name    : SqrtQueries.entry_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:21.210232+00:00
-- url     : https://prove2.me/theorems/3c17269c-e490-417d-ab1a-63fdacbfe782
-- title:
--   Proof of Proposition 3.6 — the entry $|\langle j^*+1|V_1|j^*\rangle|\ge1/10$
-- statement:
--   Let $N\ge4$ and let $V_1$ be a square root of $U_1=e^{iA/4}De^{-iA/4}$. For each $j$, let $r_j$ be the eigenvalue of $V_1$ at the eigenvector $e^{iA/4}|j\rangle$ of $U_1$. If $j^*$ satisfies $r_{j^*+1}=-\omega_{2N}r_{j^*}$ (indices modulo $N$; such a $j^*$ exists by Lemma 3.1), then
--   $$
--   \big|\langle j^*+1|\,V_1\,|j^*\rangle\big|\ge\frac1{10}.
--   $$
--
--   Since every square root of $U_0=D$ is diagonal, this off-diagonal entry witnesses Proposition 3.6, and measuring $V_1|j^*\rangle$ detects it in Algorithm 2.
--
--   **Formalization Note** $|j\rangle$ is the standard basis vector and $\langle j^*+1|V_1|j^*\rangle$ is the matrix entry in row $j^*+1$, column $j^*$. A square root is any complex matrix with $V_1V_1=U_1$; the $r_j$ are given by the hypotheses $V_1e^{iA/4}|j\rangle=r_je^{iA/4}|j\rangle$.
--
--   Differences from the source: none.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), proof of Proposition 3.6, pp.18–19

import Mathlib
import Definitions.Def_SqrtQueries_oracle

namespace SqrtQueries

open Matrix

/-- **Entry bound** in the proof of Proposition 3.6 of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), pp.18–19. Let `N ≥ 4` and let `V₁` be a
square root of `U₁ = e^{iA/4} D e^{−iA/4}`, whose eigenvalue at `e^{iA/4}|j⟩` is `r_j`. If
`r_{j*+1} = −ω_{2N} r_{j*}` (the index of Lemma 3.1), then `|⟨j*+1| V₁ |j*⟩| ≥ 1/10`.

**Formalization Note.** `|j⟩` is `Pi.single j 1`, `j* + 1` is `Fin N` addition, the entry
`⟨j*+1|V₁|j*⟩` is `V₁ (j* + 1) j*`, and `|·|` is the modulus in `ℂ`. A square root is any
complex matrix with `V₁ * V₁ = U₁`. -/
theorem entry_bound (N : ℕ) [NeZero N] (hN : 4 ≤ N) (V₁ : Matrix (Fin N) (Fin N) ℂ)
    (hV₁ : V₁ * V₁ = oracle N true) (r : Fin N → ℂ)
    (hr : ∀ j, V₁ *ᵥ (NormedSpace.exp ((Complex.I / 4) • smearA N) *ᵥ Pi.single j 1) =
      r j • (NormedSpace.exp ((Complex.I / 4) • smearA N) *ᵥ Pi.single j 1))
    (jstar : Fin N) (hj : r (jstar + 1) = -MagnonCode.AQEDC.omega (2 * N) * r jstar) :
    1 / 10 ≤ ‖V₁ (jstar + 1) jstar‖ := by sorry

end SqrtQueries
