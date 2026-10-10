-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_lemma_2_2
-- name    : ScatPoly.Inequiv.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:00.517103+00:00
-- url     : https://prove2.me/theorems/4c483324-9b6a-415f-81a8-d058d89a7216
-- title:
--   Lemma 2.2, p. 5 ([7]) — L_f = L_g forces α_0 = β_0 and two families of coefficient identities
-- statement:
--   Let $q = p^r$ with $p$ prime and $r \ge 1$, let $n \ge 1$ and let $F = \mathbb F_{q^n}$. Let
--   $$f(x) = \sum_{i=0}^{n-1} \alpha_i x^{q^i}, \qquad g(x) = \sum_{i=0}^{n-1} \beta_i x^{q^i}$$
--   be two $q$-polynomials over $F$ such that $L_f = L_g$, where $L_f = \{\langle (x, f(x))\rangle_{\mathbb F_{q^n}} : x \in \mathbb F_{q^n}^*\}$. Then $\alpha_0 = \beta_0$,
--   $$\alpha_k \alpha_{n-k}^{q^k} = \beta_k \beta_{n-k}^{q^k} \qquad (k = 1, 2, \dots, n-1),$$
--   and
--   $$\alpha_1 \alpha_{k-1}^{q} \alpha_{n-k}^{q^k} + \alpha_k \alpha_{n-1}^{q} \alpha_{n-k+1}^{q^k} = \beta_1 \beta_{k-1}^{q} \beta_{n-k}^{q^k} + \beta_k \beta_{n-1}^{q} \beta_{n-k+1}^{q^k} \qquad (k = 2, 3, \dots, n-1).$$
--
--   The paper quotes this result of Csajbók, Marino and Polverino [7] and uses it to compare the coefficients of $\psi_{h,t}$ with those of the polynomials describing an equivalent linear set (proofs of Lemmas 5.2 and 5.3).
--
--   **Formalization Note.** The coefficients are a sequence $\alpha : \mathbb N \to F$ of which only $\alpha_0, \dots, \alpha_{n-1}$ enter $f$ and the identities. The statement is for general $n$ and arbitrary $q$-polynomials, as printed.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 5, Lemma 2.2 (cited from [7] Csajbók, Marino & Polverino, JCTA 157 (2018))

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem lemma_2_2 (F : Type*) [Field F] [Fintype F] (p r n q : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 0 < r) (hq : q = p ^ r) (hn : 1 ≤ n) (hcard : Fintype.card F = q ^ n)
    (α β : ℕ → F) (hL : linSet (ScatPoly.Construction.qpoly q n α) = linSet (ScatPoly.Construction.qpoly q n β)) :
    α 0 = β 0 ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
      α k * α (n - k) ^ q ^ k = β k * β (n - k) ^ q ^ k) ∧
    (∀ k : ℕ, 2 ≤ k → k ≤ n - 1 →
      α 1 * α (k - 1) ^ q * α (n - k) ^ q ^ k + α k * α (n - 1) ^ q * α (n - k + 1) ^ q ^ k =
        β 1 * β (k - 1) ^ q * β (n - k) ^ q ^ k + β k * β (n - 1) ^ q * β (n - k + 1) ^ q ^ k) := by sorry

end ScatPoly.Inequiv
