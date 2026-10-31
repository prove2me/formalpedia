-- Prove2me | Theorems.Thm_ParriloTheta_proposition_6_7
-- name    : ParriloTheta.proposition_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:08.238812+00:00
-- url     : https://prove2.me/theorems/6587929e-8138-4b33-9c6e-8c95d4f0a5f2
-- title:
--   Proposition 6.7 (Dobre–Vera) — a $\mathcal K^{(1)}$-certificate with the symmetries of $M$
-- statement:
--   Let $M\in\mathcal K^{(1)}_n$. Then $M$ has a $\mathcal K^{(1)}$-certificate $P(1),\dots,P(n)$ such that for every permutation $\sigma$ of $[n]$ with $M_{\sigma(j)\sigma(k)}=M_{jk}$ for all $j,k$,
--   $$
--   P(\sigma(i))_{\sigma(j)\sigma(k)}=P(i)_{jk}\qquad\text{for all } i,j,k .
--   $$
--   The paper cites this result and applies it to the permutations of the added isolated nodes in §6.2.
--
--   **Formalization Note** Permutations are `Equiv.Perm ι`.
--
--   Differences from the source:
--   - reading: σ(P(i)) = P(σ(i)) for all σ with σ(M) = M (σ acting on a matrix undefined on the page) → P(σ i)_{σ j, σ k} = P(i)_{jk} for all i, j, k, for every σ with M_{σ j, σ k} = M_{jk}; reason: the natural action σ(A)_{σ(j)σ(k)} = A_{jk}; the gloss (6.3) P(i)_{σ(j)σ(k)} = P(σ(i))_{jk} agrees with it for involutions, the only permutations (transpositions) the paper applies it to
--   - encoding: [n], Sym(n) → a finite type ι, Equiv.Perm ι; reason: Lean convention
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Proposition 6.7, p.20 (cited from Dobre and Vera [8])

import Mathlib
import Definitions.Def_ParriloTheta_InK
import Definitions.Def_ParriloTheta_IsK1Cert

namespace ParriloTheta

/-- **Proposition 6.7 (Dobre and Vera [8]): a symmetric `K^(1)`-certificate.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Proposition 6.7, p.20:
"Assume that M ∈ K(1)_n. Then M has a K(1)-certificate P(1), . . . , P(n) satisfying the following
symmetry property: σ(P(i)) = P(σ(i)) for all σ ∈ Sym(n) such that σ(M) = M."

**Reading.** `σ(A)` is the matrix with `σ(A)_{σ(j)σ(k)} = A_jk`, so `σ(M) = M` means
`M_{σ(j)σ(k)} = M_jk` for all `j, k`, and `σ(P(i)) = P(σ(i))` means
`P(σ(i))_{σ(j)σ(k)} = P(i)_jk` for all `i, j, k`.

**Formalization Note.** `Sym(n)` is `Equiv.Perm ι`; `P(i)_jk` is `P i j k`. -/
theorem proposition_6_7 {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (hM : InK 1 M) :
    ∃ P : ι → Matrix ι ι ℝ, IsK1Cert M P ∧
      ∀ σ : Equiv.Perm ι, (∀ j k, M (σ j) (σ k) = M j k) →
        ∀ i j k, P (σ i) (σ j) (σ k) = P i j k := by sorry

end ParriloTheta
