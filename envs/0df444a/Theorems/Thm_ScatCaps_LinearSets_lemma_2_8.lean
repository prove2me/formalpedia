-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_lemma_2_8
-- name    : ScatCaps.LinearSets.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:54.062315+00:00
-- url     : https://prove2.me/theorems/e66a5124-3f8d-4cc4-9805-f298525bb371
-- title:
--   Lemma 2.8, p. 14 — for q = 2 some b ∈ 𝔽*_{2^{3n}} is outside the image of H(z) = (1 − z)/z^j and has norm ≠ 1
-- statement:
--   Let $n>1$, let $E=\mathbb F_{2^{6n}}$, and let $\mathbb F_{2^{3n}}$ and $\mathbb F_{2^n}$ be its subfields of orders $2^{3n}$ and $2^n$. Put $j=2^{2n+1}-1$ and
--
--   $$
--   H(z)=\frac{1-z}{z^{j}}\qquad(z\in\mathbb F_{2^{3n}}^*).
--   $$
--
--   Then there is $b\in\mathbb F_{2^{3n}}^*$ with
--
--   $$
--   b\notin\{H(z): z\in\mathbb F_{2^{3n}}^*\}\qquad\text{and}\qquad N_{2^{3n}/2^n}(b)=b^{1+2^n+2^{2n}}\neq1 .
--   $$
--
--   This supplies the coefficient $b$ for the binomial family over $\mathbb F_2$ (Proposition 2.9, Theorem 2.10).
--
--   **Formalization Note** The page names the variable of $H$ "$t$"; it is renamed $z$ to avoid a clash with the $t$ of $\mathrm{PG}(r-1,q^t)$. $\mathbb F_{2^{3n}}$ is represented as the fixed field of $x\mapsto x^{2^{3n}}$ inside a field $E$ of characteristic $2$ with $|E|=2^{6n}$, as in the other §2 statements; $j=(q^{2n+1}-1)/(q-1)$ at $q=2$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 14, Lemma 2.8

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem lemma_2_8 (E : Type*) [Field E] [Fintype E]
    (n : ℕ) [ExpChar E 2] (hn : 1 < n)
    (hE : Fintype.card E = 2 ^ (6 * n)) :
    ∃ b : E, b ∈ subfieldOf E 2 1 (3 * n) ∧ b ≠ 0 ∧
      relNorm 2 (3 * n) n b ≠ 1 ∧
      ∀ z : E, z ∈ subfieldOf E 2 1 (3 * n) → z ≠ 0 →
        b ≠ (1 - z) / z ^ (2 ^ (2 * n + 1) - 1) := by sorry

end ScatCaps.LinearSets
