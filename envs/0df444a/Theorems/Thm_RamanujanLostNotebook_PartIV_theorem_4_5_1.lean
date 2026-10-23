-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_theorem_4_5_1
-- name    : RamanujanLostNotebook.PartIV.theorem_4_5_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T12:24:58.244207+00:00
-- url     : https://prove2.me/theorems/fca2d90e-ee95-44fa-a150-de120dd5535f
-- title:
--   Karatsuba's monotonicity theorem for h
-- statement:
--   The function $h(x)=\left(\left(\frac{e}{x}\right)^x\frac{\Gamma(1+x)}{\sqrt\pi}\right)^6-(8x^3+4x^2+x)$ is strictly increasing on $(1,\infty)$, $h(1)=e^6/\pi^3-13$, and $h$ maps $(1,\infty)$ onto the open interval $(h(1),1/30)$. Differs from the printed source: no change of content; increasing is read as strictly increasing, and for $1<x\le 4.21$ the book relies on Karatsuba's cited computations.
--
--   **Discrepancy from the printed source.** No difference in content from Theorem 4.5.1, pp. 118-119. 'Monotonically increasing' is read as strictly increasing (our reading; the proof shows h' > 0). The book gives the argument in full only for x >= 4.21 (Lemmas 4.5.1-4.5.2) and refers to Karatsuba's paper for the computations on 1 < x <= 4.21 (Lemma 4.5.3), so on that range the statement rests on the cited source, not on the book's text.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 4, Theorem 4.5.1, p. 118, eq. (4.5.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_ch04_ramanujanGammaH

namespace RamanujanLostNotebook.PartIV
theorem theorem_4_5_1 :
    StrictMonoOn ramanujanGammaH (Set.Ioi 1) ∧
    ramanujanGammaH 1 = Real.exp 6 / Real.pi ^ (3 : ℕ) - 13 ∧
    ramanujanGammaH '' Set.Ioi 1 =
      Set.Ioo (Real.exp 6 / Real.pi ^ (3 : ℕ) - 13) (1 / 30) := by sorry
end RamanujanLostNotebook.PartIV
