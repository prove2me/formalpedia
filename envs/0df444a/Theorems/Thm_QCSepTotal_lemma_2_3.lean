-- Prove2me | Theorems.Thm_QCSepTotal_lemma_2_3
-- name    : QCSepTotal.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:41:16.363193+00:00
-- url     : https://prove2.me/theorems/9c2079ec-956d-4e59-957d-8c0a2c5e28a4
-- title:
--   Lemma 2.3 — linear strong $(2b,\varepsilon)$-seeded extractor with seed length $\lceil K_E\log^2 b\rceil$ and surjective fixed-seed maps
-- statement:
--   Fix $0<\varepsilon\le1/2$. There is a constant $K_E>0$ such that, for every sufficiently large integer $b$, with
--   $$c=\lceil K_E\log^2 b\rceil ,$$
--   there is a strong $(2b,\varepsilon)$-seeded extractor $E:\mathbb F_2^{4b}\times\mathbb F_2^c\to\mathbb F_2^b$ whose fixed-seed maps $E_j:\mathbb F_2^{4b}\to\mathbb F_2^b$ are all linear over $\mathbb F_2$ and surjective. Logarithms are binary.
--
--   This is the extractor that compresses the lookup table of the construction into one cell of length $4b$; linearity lets the certificate at any address be shared additively, and surjectivity keeps $E_\ell(U)$ uniform.
--
--   **Formalization Note** $E$ is given by its family of fixed-seed linear maps, and the extractor is $(u,j)\mapsto E_j(u)$.
--
--   Differences from the source:
--   - encoding: E : F₂^{4b} × F₂^c → F₂^b with linear fixed-seed maps → a seed-indexed family of ZMod 2-linear maps E j; reason: a map with linear fixed-seed maps is exactly such a family
--   - reading: for every sufficiently large integer b → there is b₀ with the conclusion for every b ≥ b₀; reason: the standard meaning of 'sufficiently large'
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Lemma 2.3, p.4

import Mathlib
import Definitions.Def_QCSepTotal_IsStrongExtractor

namespace QCSepTotal

/-- **Lemma 2.3** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.4). Fix a constant `0 < ε ≤ 1/2`. There is a constant `K_E > 0` such that,
for every sufficiently large integer `b`, the choice `c = ⌈K_E log² b⌉` admits a strong
`(2b, ε)`-seeded extractor `E : F₂^{4b} × F₂^c → F₂^b` whose fixed-seed maps
`E_j : F₂^{4b} → F₂^b` are linear over `F₂` and surjective.

**Formalization Note.** `E` is given by its fixed-seed maps `E j`, linear by type; the
extractor is `(u, j) ↦ E j u` (source first, seed second, as in (3)). Logarithms are binary
(p.3) and `log² b` is `(log₂ b)²`. "Sufficiently large" is "at least some `b₀`". -/
theorem lemma_2_3 (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ∃ KE : ℝ, 0 < KE ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      ∃ E : (Fin ⌈KE * Real.logb 2 b ^ 2⌉₊ → ZMod 2) → (Fin (4 * b) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2),
        (∀ j, Function.Surjective (E j)) ∧ IsStrongExtractor (fun u j => E j u) (2 * (b : ℝ)) ε := by sorry

end QCSepTotal
