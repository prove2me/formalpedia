-- Prove2me | Theorems.Thm_ScatCaps_Caps_lemma_2_8
-- name    : ScatCaps.Caps.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:09.703734+00:00
-- url     : https://prove2.me/theorems/526c1c0b-53f0-48f8-889f-d2c4f6b93286
-- title:
--   Lemma 2.8, p. 14 — some b ∈ 𝔽*_{2^{3n}} lies outside the image of H(t) = (1 − t)/t^j and has N_{2^{3n}/2^n}(b) ≠ 1
-- statement:
--   Let $n > 1$ and $q = 2$, and consider the function $H(s) = (1 - s)/s^j$ on $\mathbb F^*_{2^{3n}}$, where
--
--   $$j = \frac{q^{2n+1} - 1}{q - 1} = 2^{2n+1} - 1 .$$
--
--   Then there exists $b \in \mathbb F^*_{2^{3n}}$ such that $b \notin \{H(s) : s \in \mathbb F^*_{2^{3n}}\}$ and $N_{2^{3n}/2^n}(b) \ne 1$.
--
--   This provides the coefficient $b$ for the binomial scattered linear set of Theorem 2.10 via Proposition 2.9.
--
--   **Formalization Note** $\mathbb F_{2^{3n}}$ is realized as the subfield of order $2^{3n}$ of an ambient field $E$ with $|E| = 2^{6n}$ (the field of Theorem 2.10); the statement is intrinsic to $\mathbb F_{2^{3n}}$. The characteristic-2 instance is stated explicitly although it follows from $|E| = 2^{6n}$. The variable of $H$ is written $s$ to avoid a clash with $t$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 14, Lemma 2.8

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.Caps

theorem lemma_2_8 (E : Type*) [Field E] [Fintype E] [CharP E 2] (n : ℕ) (hn : 1 < n)
    (hE : Fintype.card E = 2 ^ (6 * n)) :
    ∃ b ∈ ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n), b ≠ 0 ∧
      (∀ s ∈ ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n), s ≠ 0 → (1 - s) / s ^ (2 ^ (2 * n + 1) - 1) ≠ b) ∧
      ScatCaps.LinearSets.relNorm 2 (3 * n) n b ≠ 1 := by sorry

end ScatCaps.Caps
