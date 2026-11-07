-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_7
-- name    : RandOrderSort.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:35.515602+00:00
-- url     : https://prove2.me/theorems/f630a508-4003-4333-b762-7bf88f91af5f
-- title:
--   Lemma 4.7 — child interval lengths from an i.i.d. prefix
-- statement:
--   Let an observed prefix of $m$ independent uniform samples in $[0,1]$ define an empirical partition tree with $b\le m$ leaves, where $b$ is a power of two. Fix a deterministic cut $q\in(0,1)$ and a level with $2s$ leaves per parent, and let $J_q$ be the parent containing $q$. Each of its two children contains $s$ consecutive buckets, with nominal length $p=s/b$ and nominal sample count $r=mp$. If $r\ge 1024$, then
--   $$\mathbb P\bigl(\exists\text{ child }I\text{ of }J_q:|I|\notin[15p/16,17p/16]\bigr)\le A_pe^{-a_pr},\qquad A_p=2+2(8195)^2,\quad a_p=\frac1{14336}.$$
--   The constants are uniform in $q,m,b,s$, including cuts outside the observed range of the prefix.
--
--   Here $|I|$ denotes the length of $I\cap[0,1]$. Empirical bucket boundaries control observation counts, while this lemma controls the interval lengths, which remain random.
--
--   Differences from the source:
--   - encoding: the empirical tree on independent uniform samples, whose keys are almost surely distinct → the tree on the order by value with ties broken by index (`ltOf Y 1 1`); reason: ties have probability zero
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.7, p.25, display (30)

import Mathlib
import Definitions.Def_RandOrderSort_mkTree
import Definitions.Def_RandOrderSort_iidUnif
import Definitions.Def_RandOrderSort_Wi

namespace RandOrderSort

/-- **Lemma 4.7 (Child interval lengths from an i.i.d. prefix)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.25: "Let an observed prefix
of m independent uniform samples in [0, 1] define an empirical partition tree with b ≤ m leaves, where
b is a power of two. Fix a deterministic cut q ∈ (0, 1) and a level with 2s leaves per parent. Let J_q
be the parent containing q. Each of its two children contains s consecutive buckets, with nominal
length p = s/b and nominal sample count r = mp. If r ≥ 1024, then
P(∃ child I of J_q : |I| ∉ [15p/16, 17p/16]) ≤ A_p e^{−a_p r}, (30) where one may take
A_p = 2 + 2(8195)², a_p = 1/14336. The constants are uniform in q, m, b, s, including cuts outside the
observed range of the prefix."

**Formalization Note.** The `mm` samples `Y` have law `iidUnif mm`; the tree is (7) on them with `bb`
leaves (`mkTree`, value ties broken by index, a null event); the level is `s = 2^h`, `J_q` the node of
height `h + 1` containing `q`, its children the nodes `(h, 2·idx)`, `(h, 2·idx + 1)`; `|I|` is the
length of `I ∩ [0,1]` (p.23). -/
theorem lemma_4_7 : ∀ (mm bb : ℕ), (∃ e, bb = 2 ^ e) → bb ≤ mm → ∀ q : ℝ, 0 < q → q < 1 →
    ∀ h : ℕ, 2 ^ (h + 1) ≤ bb → 1024 ≤ (mm : ℝ) * ((2 : ℝ) ^ h / bb) →
      iidUnif mm {Y | ∃ c < 2,
          ¬ (15 / 16 * ((2 : ℝ) ^ h / bb) ≤
                clipLen (vecVal Y) (mkTree (ltOf Y 1 1) (Finset.range mm) bb) h
                  (2 * (cutLeaf (fun a => decide (q < vecVal Y a))
                    (mkTree (ltOf Y 1 1) (Finset.range mm) bb) / 2 ^ (h + 1)) + c) ∧
              clipLen (vecVal Y) (mkTree (ltOf Y 1 1) (Finset.range mm) bb) h
                  (2 * (cutLeaf (fun a => decide (q < vecVal Y a))
                    (mkTree (ltOf Y 1 1) (Finset.range mm) bb) / 2 ^ (h + 1)) + c) ≤
                17 / 16 * ((2 : ℝ) ^ h / bb))} ≤
        ENNReal.ofReal (Ap * Real.exp (-(1 / 14336 * ((mm : ℝ) * ((2 : ℝ) ^ h / bb))))) := by sorry

end RandOrderSort
