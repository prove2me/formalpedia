-- Prove2me | Theorems.Thm_QaryCVP_lemma_4_3
-- name    : QaryCVP.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:19.513139+00:00
-- url     : https://prove2.me/theorems/dd9fd1db-65b1-40b4-ac55-f65e19ae23b7
-- title:
--   Lemma 4.3 — Erdős–Rényi identity $\mathbb E_{C,s}[(\mathbb E_u\Phi(s-Cu))^2]=2^{-\ell}\mathbb E_s[\Phi(s)^2]$
-- statement:
--   Let $G$ be a finite abelian group and $\ell\ge1$. Let $s$ be uniform in $G$ and $\Phi:G\to\mathbb R$ a fixed function with $\mathbb E_s[\Phi(s)]=0$. Choose $C\in G^\ell$ with independent uniform columns, independently of $s$, and let $u$ be independent and uniform in $\{0,1\}^\ell$, where $Cu=\sum_{i:u_i=1}C_i$. Then
--
--   $$\mathbb E_{C,s}\Big[\big(\mathbb E_u[\Phi(s-Cu)]\big)^2\Big]=2^{-\ell}\,\mathbb E_s\big[\Phi(s)^2\big].$$
--
--   It is the second-moment identity behind the passage from average success to success for every right-hand side (Lemma 4.4).
--
--   **Formalization Note** All expectations are finite uniform averages, written as sums.
--
--   Differences from the source: none.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.3, pp.35–36

import Mathlib

namespace QaryCVP

/-- **Lemma 4.3** (Erdős–Rényi second-moment identity). Kim, Kwon, Lee, Lee, STOC 2027 submission
manuscript (sha256 9aeb2ff4…ab4), Lemma 4.3, pp.35–36.

Let `G` be a finite abelian group and `ℓ ≥ 1`. Let `s` be uniform in `G` and `Φ : G → R` a fixed
function with `E_s[Φ(s)] = 0`. Choose `C ∈ G^ℓ` with independent uniform columns, independently of
`s`, and `u` independent and uniform in `{0, 1}^ℓ`, where `Cu = Σ_{i : uᵢ = 1} Cᵢ`. Then
`E_{C,s}[(E_u[Φ(s − Cu)])²] = 2^{−ℓ} E_s[Φ(s)²]`.

**Formalization Note.** All expectations are finite uniform averages; `E_s[Φ] = 0` is `Σ_s Φ(s) = 0`. -/
theorem lemma_4_3 {G : Type} [AddCommGroup G] [Fintype G] (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (Φ : G → ℝ)
    (hΦ : ∑ s, Φ s = 0) :
    (∑ C : Fin ℓ → G, ∑ s : G,
        ((∑ u : Fin ℓ → Bool, Φ (s - ∑ i, if u i then C i else 0)) / (2 : ℝ) ^ ℓ) ^ 2) /
      ((Fintype.card G : ℝ) ^ ℓ * Fintype.card G) =
    (1 / 2 : ℝ) ^ ℓ * ((∑ s, Φ s ^ 2) / Fintype.card G) := by sorry

end QaryCVP
