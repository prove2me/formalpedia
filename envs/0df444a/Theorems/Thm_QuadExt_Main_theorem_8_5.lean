-- Prove2me | Theorems.Thm_QuadExt_Main_theorem_8_5
-- name    : QuadExt.Main.theorem_8_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:33.486365+00:00
-- url     : https://prove2.me/theorems/15628fac-371f-4ade-996b-e383d1bbf08d
-- title:
--   Theorem 8.5 — the large-field family $(W(\beta))_{ji} = \lambda_i^{j-1}\beta^{w_i}$ is a $(d, \sqrt d/(2m), \varepsilon)$-rank combiner of size $|F|$
-- statement:
--   Let $F$ be a finite field, $\varepsilon > 0$, $|F| \ge 16 m n^2/\varepsilon$ and $m \le \sqrt d / 2$. Let $\lambda_1, \dots, \lambda_n \in F$ be distinct and non-zero, and let $w_1, \dots, w_n$ be distinct positive integers with $\max_i w_i \le 8n^2$ forming a Sidon set. Then the family $\{W(\beta)\}_{\beta \in F}$ of matrices in $F^{m \times n}$,
--   $$\big(W(\beta)\big)_{ji} = \lambda_i^{\,j-1}\, \beta^{w_i},$$
--   is a $(d, \sqrt d/(2m), \varepsilon)$-rank combiner over $F$ with output length $m$ and size $|F|$. This is the paper's explicit rank combiner over large fields; Theorem 8.9 then reduces the field to $\mathbb F_2$.
--
--   Differences from the source:
--   - generalization: "there exists an explicit $(d, \sqrt d/(2m), \varepsilon)$-rank combiner" → the construction of the proof is one for every admissible choice of $\lambda$ and $w$; reason: the proof chooses "an arbitrary set" of such $\lambda_i$ and Sidon weights, and the existence claim follows because such choices exist whenever the statement is non-trivial ($|F| > n$ when $\varepsilon < 1 \le m$; Sidon sets in $[8n^2]$ by [ET41]).
--   - encoding: $\varepsilon > 0$ assumed; reason: the hypothesis $|F| \ge 16mn^2/\varepsilon$ presupposes it.
--   - encoding: row index $j \in [m]$ → `j : Fin m` (0-based), so $\lambda_i^{j-1}$ is written $\lambda_i^j$; $d$ natural; reason: index convention.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 26 (PDF 27), Theorem 8.5 and its proof

import Mathlib
import Definitions.Def_QuadExt_Main_RankCombiner

namespace QuadExt.Main

/-- **Theorem 8.5** (p. 26), "explicit" read as the construction of its proof: over any finite
field `F` with `|F| ≥ 16mn²/ε` and `m ≤ √d/2`, for every choice of distinct non-zero
`λ_1, …, λ_n ∈ F` and positive integers `w_1, …, w_n ≤ 8n²` forming a Sidon set, the family
`{W(β)}_{β∈F}`, `(W(β))_{ji} = λ_i^{j−1} β^{w_i}`, is a `(d, √d/(2m), ε)`-rank combiner over `F`
with output length `m` and size `|F|`. -/
theorem theorem_8_5 {F : Type} [Field F] [Fintype F] (n m d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hF : 16 * (m : ℝ) * (n : ℝ) ^ 2 / ε ≤ Fintype.card F)
    (hm : (m : ℝ) ≤ Real.sqrt d / 2)
    (lam : Fin n → F) (hlam_inj : Function.Injective lam) (hlam_ne : ∀ i, lam i ≠ 0)
    (w : Fin n → ℕ) (hw_inj : Function.Injective w) (hw_pos : ∀ i, 0 < w i)
    (hw_le : ∀ i, w i ≤ 8 * n ^ 2) (hw_sidon : IsSidon (Finset.univ.image w)) :
    IsRankCombiner d (Real.sqrt d / (2 * m)) ε (largeFieldCombiner (m := m) lam w) := by sorry

end QuadExt.Main
