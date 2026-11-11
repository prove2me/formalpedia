-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_corollary_3_14
-- name    : RandProdExp.TwoSided.corollary_3_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:18:33.710985+00:00
-- url     : https://prove2.me/theorems/a309ab37-adf4-479f-b4b5-764cd244df37
-- title:
--   Corollary 3.14 — the anchor sets $\Omega^\cap_I(M)$ of $\mathcal P_\cap(M)$ are $2^D\varepsilon$-sparse
-- statement:
--   Let $D\ge1$, $n\ge2$, and let $M\subsetneq[n]^D$ be $\varepsilon$-closed with $0<2^D\varepsilon<1$. Then for every $I\subsetneq[D]$ the anchor set
--   $$\Omega^\cap_I(M)=\{a\in[n]^{I^c}:\ P(I,a)\in\mathcal P_\cap(M)\}$$
--   is $(2^D\varepsilon)$-sparse in $[n]^{I^c}$. It extends Lemma 3.13 from the maximal planes to their intersection closure, which indexes the blocks of the plane-interaction matrix.
--
--   Differences from the source:
--   - encoding: standing assumption of §3.1 (p. 19): integers D ≥ 1 and n ≥ 2 → explicit hypotheses 1 ≤ D and 2 ≤ n; reason: stated once at the top of §3.1 for the whole paper; makes the anchor of a plane unique
--   - encoding: [n] = {1, …, n}; points of [n]^D; axis-parallel lines L(n, D) → Fin n; functions Fin D → Fin n; the line in direction j through x is axisLine j x (every line arises this way); reason: Lean indexing convention; same lines, same sets
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 23, Corollary 3.14

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid

namespace RandProdExp.TwoSided

/-- **Corollary 3.14** (p. 23). Let `M ⊊ [n]^D` be ε-closed with `0 < 2^D ε < 1`. Then for every
`I ⊊ [D]`, the anchor set `Ω∩_I(M) ⊆ [n]^{I^c}` of the `I`-planes of `P∩(M)` is `(2^D ε)`-sparse.
(Standing assumptions of §3.1: `D ≥ 1`, `n ≥ 2`.) -/
theorem corollary_3_14 (D n : ℕ) (hD : 1 ≤ D) (hn : 2 ≤ n) (ε : ℝ)
    (hε0 : 0 < (2 : ℝ) ^ D * ε) (hε1 : (2 : ℝ) ^ D * ε < 1)
    (M : Set (Fin D → Fin n)) (hMne : M ≠ Set.univ) (hM : IsEpsClosed ε M)
    (I : Finset (Fin D)) (hI : I ≠ Finset.univ) :
    IsEpsSparse ((2 : ℝ) ^ D * ε) (capAnchorSet I M) := by sorry

end RandProdExp.TwoSided
