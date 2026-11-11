-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_8_3
-- name    : QuadExt.Main.lemma_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:04:38.114205+00:00
-- url     : https://prove2.me/theorems/4babae1d-2e5a-4db0-be6f-4b14ef53b1c5
-- title:
--   Lemma 8.3 — a $(d, r, \varepsilon)$-rank combiner gives an $(\varepsilon, 2^{(m-r)/2})$ extractor for derivative-entropy-$d$ quadratic sources and an $(\varepsilon, 0)$ one for affine sources
-- statement:
--   Let $W_1, \dots, W_N \in \mathbb F_2^{m \times n}$ be a $(d, r, \varepsilon)$-rank combiner and define $L : \mathbb F_2^n \times [N] \to \mathbb F_2^m$ by
--   $$L(x, i) = W_i\, x .$$
--   Then
--
--   1. $L$ is an $(\varepsilon, 2^{(m-r)/2})$-strong linear seeded extractor for the class of quadratic sources $X = f(U_k)$ with $H_\infty(\partial_a f(U_k)) \ge d$ for all non-zero $a$;
--   2. $L$ is an $(\varepsilon, 0)$-strong linear seeded extractor for affine sources with entropy at least $d$.
--
--   The point of item 1 is that the closeness error on good seeds, $2^{(m-r)/2}$, can be far smaller than the inverse of the number of seeds, which a linear seeded extractor for general sources cannot achieve.
--
--   Differences from the source:
--   - encoding: seeds $[N]$ → `Fin N`, with $N \ge 1$ required by the definitions of a rank combiner and of a seeded extractor; reason: a uniform seed in $[N]$ presupposes $N \ge 1$, and the condition appears on both sides.
--   - reading: quadratic sources $X = f(U_k)$ with $H_\infty(\partial_a f) \ge d$ for all non-zero $a$, and square matrices $G_i \in F^{k \times k}$ in Definition 8.2 → $k \ge 1$ in both; reason: at $k = 0$ "for all non-zero $a$ (resp. $y$)" is vacuous, a constant source would enter the class of item 1 and no family with $r > 0$, $\varepsilon < 1$ would be a rank combiner; the proof's matrices $G_i \in \mathbb F_2^{k \times k}$ act on non-zero vectors.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 25 (PDF 26), Lemma 8.3

import Mathlib
import Definitions.Def_QuadExt_Main_SeededExt
import Definitions.Def_QuadExt_Main_RankCombiner

namespace QuadExt.Main

/-- **Lemma 8.3** (p. 25): if `W_1, …, W_N ∈ 𝔽₂^{m×n}` is a `(d, r, ε)`-rank combiner, then
`L(x, i) = W_i x` is (1) an `(ε, 2^{(m−r)/2})`-strong linear seeded extractor for quadratic sources
`f(U_k)` with `H_∞(∂_a f) ≥ d` for all `a ≠ 0`, and (2) an `(ε, 0)`-strong linear seeded extractor
for affine sources with entropy at least `d`. -/
theorem lemma_8_3 (n m N d : ℕ) (r ε : ℝ) (W : Fin N → Matrix (Fin m) (Fin n) (ZMod 2))
    (hW : IsRankCombiner d r ε W) :
    IsSLSEFor (QuadDerivClass n d) ε ((2 : ℝ) ^ (((m : ℝ) - r) / 2))
        (fun x i => Matrix.mulVec (W i) x) ∧
      IsSLSEFor (AffineClass n d) ε 0 (fun x i => Matrix.mulVec (W i) x) := by sorry

end QuadExt.Main
