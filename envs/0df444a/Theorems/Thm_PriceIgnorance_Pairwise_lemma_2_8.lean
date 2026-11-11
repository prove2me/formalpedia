-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_2_8
-- name    : PriceIgnorance.Pairwise.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:15.558044+00:00
-- url     : https://prove2.me/theorems/e4c618b8-409c-4dc2-95dd-25c69f8c3ff4
-- title:
--   Lemma 2.8 — the expected total variation of the empirical distribution of $C$ samples is at most $\tfrac12\sqrt{s/C}$
-- statement:
--   Let $D$ be a distribution on $[n]$ with support size $s$, let $C\ge1$, and let $\widehat D$ be the empirical distribution of $C$ i.i.d. samples $Y_1,\dots,Y_C\sim D$, that is $\widehat D(x)=\frac1C\sum_{i=1}^C\mathbf 1[Y_i=x]$. Then
--   $$\mathbb E_{Y_1,\dots,Y_C\overset{iid}\sim D}\Big[d_{TV}(D,\widehat D)\Big]\ \le\ \frac12\sqrt{\frac sC}.$$
--
--   In Theorem 3.16 this shows that the empirical law seen by a correlation-blind algorithm approaches the witness law as the number $C$ of hidden samples grows.
--
--   Differences from the source:
--   - encoding: [n], D a distribution of support size s, C samples → Fin n, D : PMF (Fin n), s = |supp D| (defined, not a free parameter), C ≥ 1 as [NeZero C]; reason: the empirical distribution (1/C) Σ 1[Y_i = x] requires C ≥ 1
--   - encoding: expectation over Y_1..Y_C iid ∼ D → the PMF expectation under the published i.i.d. law QCSepTotal.iidLaw D C; reason: same law on Fin C → Fin n
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 4, Lemma 2.8

import Mathlib
import Definitions.Def_QCSepTotal_tv
import Definitions.Def_PriceIgnorance_Pairwise_Empirical

namespace PriceIgnorance.Pairwise

/-- Lemma 2.8 (p. 4): for a distribution `D` on `[n]` with support size `s` and the empirical
distribution `D̂` of `C ≥ 1` i.i.d. samples from `D`, `E[d_TV(D, D̂)] ≤ ½ √(s / C)`. -/
theorem lemma_2_8 {n : ℕ} (D : PMF (Fin n)) (C : ℕ) [NeZero C] :
    pmfExp (QCSepTotal.iidLaw D C) (fun Y => QCSepTotal.tv D (empirical Y)) ≤
      (1 / 2) * Real.sqrt ((supportSize D : ℝ) / C) := by sorry

end PriceIgnorance.Pairwise
