-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_lemma_3_13
-- name    : RandProdExp.TwoSided.lemma_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:18:30.648207+00:00
-- url     : https://prove2.me/theorems/6ecbaccc-c747-4d15-be09-191878f048cc
-- title:
--   Lemma 3.13 — the anchor set $\Omega_I(M)$ of the maximal planes of an $\varepsilon$-closed set is $\varepsilon$-sparse
-- statement:
--   Let $D\ge1$, $n\ge2$, $0<\varepsilon<1$, and let $M\subsetneq[n]^D$ be $\varepsilon$-closed. Then for every $I\subsetneq[D]$ the anchor set $\Omega_I(M)=\{a\in[n]^{I^c}:P(I,a)\in\mathcal P(M)\}$ of the maximal $I$-planes of $M$ is $\varepsilon$-sparse in $[n]^{I^c}$, and consequently
--   $$|\Omega_I(M)|\le\varepsilon\, n^{D-|I|}.$$
--   This is the sparsity of maximal planes that later bounds the plane-interaction matrix.
--
--   Differences from the source:
--   - encoding: standing assumption of §3.1 (p. 19): integers D ≥ 1 and n ≥ 2 → explicit hypotheses 1 ≤ D and 2 ≤ n; reason: stated once at the top of §3.1 for the whole paper; makes the anchor of a plane unique
--   - encoding: [n] = {1, …, n}; points of [n]^D; axis-parallel lines L(n, D) → Fin n; functions Fin D → Fin n; the line in direction j through x is axisLine j x (every line arises this way); reason: Lean indexing convention; same lines, same sets
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 22, Lemma 3.13

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid

namespace RandProdExp.TwoSided

/-- **Lemma 3.13** (p. 22). Let `0 < ε < 1` and let `M ⊊ [n]^D` be ε-closed. Then for any `I ⊊ [D]`,
the anchor set `Ω_I(M) ⊆ [n]^{I^c}` of the maximal `I`-planes of `M` is ε-sparse; consequently
`|Ω_I(M)| ≤ ε n^{D − |I|}`. (Standing assumptions of §3.1: `D ≥ 1`, `n ≥ 2`.) -/
theorem lemma_3_13 (D n : ℕ) (hD : 1 ≤ D) (hn : 2 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (M : Set (Fin D → Fin n)) (hMne : M ≠ Set.univ) (hM : IsEpsClosed ε M)
    (I : Finset (Fin D)) (hI : I ≠ Finset.univ) :
    IsEpsSparse ε (anchorSet I M) ∧
      ((anchorSet I M).ncard : ℝ) ≤ ε * (n : ℝ) ^ (D - I.card) := by sorry

end RandProdExp.TwoSided
