-- Prove2me | Theorems.Thm_SYKLearn_lemma_A_4
-- name    : SYKLearn.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:35.996994+00:00
-- url     : https://prove2.me/theorems/99b37b1f-ca46-4590-a002-184906169412
-- title:
--   Lemma A.4 — commutators as contractions: $[H_u,H_h]|_{\mathbb M_6}=-2\mathsf O_1(u)h$ ($k=4$), $2\mathsf O_3(u)h$ ($k=8$)
-- statement:
--   Let $u\in\mathbb M_k$ with $k\in\{4,8\}$ and $h\in\mathbb M_4$, and let $H_v=\sum_Sv_S\Gamma_S$. With the contraction operator $\mathsf O_r(u)=\sum_{|I|=r}a_I(u)\wedge a_I$,
--
--   $$[H_u,H_h]\big|_{\mathbb M_6}=\begin{cases}-2\,\mathsf O_1(u)h,&k=4,\\ \ \ 2\,\mathsf O_3(u)h,&k=8,\end{cases}\qquad\text{and, if }k=4,\quad [H_u,H_h]\big|_{\mathbb M_2}=2\,\mathsf O_{3,4}(u)h .$$
--
--   Here $X|_{\mathbb M_j}$ is the vector of coefficients of $X$ on the degree-$j$ monomials $\Gamma_S$, $|S|=j$.
--
--   This identity turns the degree-six part of a commutator, which is what the direction matrix $M_\beta$ measures, into a linear map of $h$ built from contractions of $u$. It is used with $u=g$ and with $u=\bar\rho_4,\bar\rho_8$.
--
--   **Formalization Note** The restriction is computed as $\mathrm{Tr}[\Gamma_S^\dagger X]$ (normalized trace) and is complex; the identities assert that it equals the real vector on the right. The statement is pure algebra and holds for every $n$.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: X|M_k, the degree-k component of X read as a vector of M_k → the coefficients Tr[Γ_S^† X] (normalized trace) on k-sets S; reason: the Γ_S are orthonormal for the normalized Hilbert–Schmidt product, so these are the coefficients of X in the basis Γ_S
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma A.4, p.14 (reprinted with proof, pp.49–50)

import Mathlib
import Definitions.Def_SYKLearn_Exterior

noncomputable section
open SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma A.4**, p.14 (reprinted p.49) (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning SYK
Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Let `u ∈ M_k`, `k ∈ {4, 8}` and
`h ∈ M_4`, and `O_r(u) = Σ_{|I|=r} a_I(u) ∧ a_I`. Then `[H_u, H_h]|M_6 = −2 O_1(u) h` if `k = 4`
and `= 2 O_3(u) h` if `k = 8`. Moreover, if `k = 4`, `[H_u, H_h]|M_2 = 2 O_{3,4}(u) h`.

**Formalization Note.** `X|M_j` is the vector of coefficients `coeff Q X S = Tr[Γ_S^† X]` of
`X` on `j`-sets `S` (complex; the identity asserts it equals the real vector on the right).
`H_v = ham Q v`; `O_r(u)h = contr r u h`. The two cases `k = 4`, `k = 8` are the two conjuncts.
Pure algebra: it holds for every CAR family of a `Model` and every `N`. -/
theorem lemma_A_4 {N : ℕ} (Q : Model N) :
    (∀ u h : Ext N, IsHomog 4 u → IsHomog 4 h →
      (∀ S : Finset (Fin N), S.card = 6 →
        coeff Q (ham Q u * ham Q h - ham Q h * ham Q u) S = ((-2 * contr 1 u h S : ℝ) : ℂ)) ∧
      (∀ S : Finset (Fin N), S.card = 2 →
        coeff Q (ham Q u * ham Q h - ham Q h * ham Q u) S = ((2 * contr 3 u h S : ℝ) : ℂ))) ∧
    (∀ u h : Ext N, IsHomog 8 u → IsHomog 4 h →
      ∀ S : Finset (Fin N), S.card = 6 →
        coeff Q (ham Q u * ham Q h - ham Q h * ham Q u) S = ((2 * contr 3 u h S : ℝ) : ℂ)) := by sorry

end SYKLearn
