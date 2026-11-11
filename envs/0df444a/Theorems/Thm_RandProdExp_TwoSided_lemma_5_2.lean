-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_lemma_5_2
-- name    : RandProdExp.TwoSided.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:19:35.847175+00:00
-- url     : https://prove2.me/theorems/74abde88-f5ae-46c4-ba47-54008c6c21ec
-- title:
--   Lemma 5.2 ([KP25, Lemma 19]) — if every $\varepsilon$-closed set is inner-generated, $(C_i)$ is $\gamma(\varepsilon,D)$-product expanding
-- statement:
--   Let $K$ be any field, $D\ge1$, $n\ge2$, let $C_1,\dots,C_D\subsetneq K^n$ be codes and let $0<\varepsilon\le1$. If every $\varepsilon$-closed subset of $[n]^D$ is inner-generated in $\boxplus_iC_i$, then $(C_i)_{i\in[D]}$ is $\gamma(\varepsilon,D)$-product expanding, where
--   $$\gamma(\varepsilon,D)=\frac{\varepsilon^D}{D(2^D+1)^D}.$$
--   It is the combinatorial half of the goal: inner-generatedness of all $\varepsilon$-closed sets suffices for product expansion.
--
--   Differences from the source:
--   - encoding: standing assumption of §3.1 (p. 19): integers D ≥ 1 and n ≥ 2 → explicit hypotheses 1 ≤ D and 2 ≤ n; reason: stated once at the top of §3.1 for the whole paper; makes the anchor of a plane unique
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 34, Lemma 5.2 (Lemma 19 of [KP25])

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Codes
import Definitions.Def_RandProdExp_TwoSided_Params

namespace RandProdExp.TwoSided

/-- **Lemma 5.2** (Lemma 19 of [KP25], p. 34). Let `C_1, …, C_D ⊊ K^n` be codes over any field `K` and
let `0 < ε ≤ 1`. If every ε-closed subset of `[n]^D` is inner-generated in `⊞_i C_i`, then `(C_i)` is
`γ(ε, D)`-product expanding, `γ(ε, D) = ε^D / (D (2^D + 1)^D)`.
(Standing assumptions of §3.1: `D ≥ 1`, `n ≥ 2`.) -/
theorem lemma_5_2 {K : Type} [Field K] (D n : ℕ) (hD : 1 ≤ D) (hn : 2 ≤ n)
    (C : Fin D → Submodule K (Fin n → K)) (hC : ∀ i, C i ≠ ⊤)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h : ∀ M : Set (Fin D → Fin n), IsEpsClosed ε M → InnerGenerated M C) :
    IsProductExpanding (gammaConst ε D) C := by sorry

end RandProdExp.TwoSided
