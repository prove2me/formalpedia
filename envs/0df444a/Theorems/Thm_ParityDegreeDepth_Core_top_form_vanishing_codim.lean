-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_top_form_vanishing_codim
-- name    : ParityDegreeDepth.Core.top_form_vanishing_codim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:44.152529+00:00
-- url     : https://prove2.me/theorems/2b3bfee5-3c88-5740-801f-b36f08ebef00
-- title:
--   Eq. (7): $c(\Delta^j p)\le 2^{2j-3}\log_2\|\widehat f\|_1$ for $\deg p\le j$, $j\ge3$
-- statement:
--   Let $j\ge 3$ and let $p:\mathbb F_2^n\to\mathbb F_2$ have degree at most $j$, i.e. all $(j+1)$-fold finite differences of $p$ vanish; let $f=(-1)^p$. Then there is a subspace $U\le\mathbb F_2^n$ on which the top form $T=\Delta^j p$ vanishes,
--
--   $$
--   \Delta_{u_1}\cdots\Delta_{u_j}p(0)=0\qquad(u_1,\dots,u_j\in U),
--   $$
--
--   and whose codimension is at most
--
--   $$
--   n-\dim U\;\le\;2^{2j-3}\log_2\|\widehat f\|_1 .
--   $$
--
--   This is the key bound (7) of the source, $c(\Delta^j p)\le 2^{2j-3}\log_2\|\widehat f\|_1$, obtained in Corollary 3.8 from $c(T)\le R\le 2^{j-2}M(T)\le 2^{2j-3}\log_2\|\widehat f\|_1$. By Lemma 2.4, $p$ has degree at most $j-1$ on every coset of $U$, so querying a basis of $U^\perp$ lowers the degree on every branch.
--
--   **Formalization Note** Differences are written as the left fold `(List.ofFn h).foldl (fun q v y => q (y + v) + q y) p`.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §3.1 eq. (7), Corollaries 3.4 and 3.8 (combining Lemmas 3.2, 3.3, Theorem 3.5, Lemma 3.7), pp. 5-10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

theorem ParityDegreeDepth.Core.top_form_vanishing_codim {n j : ℕ} (hj : 3 ≤ j)
    (p : (Fin n → ZMod 2) → ZMod 2)
    (hp : ∀ (h : Fin (j + 1) → Fin n → ZMod 2) (x : Fin n → ZMod 2),
      (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p x = 0) :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ h : Fin j → Fin n → ZMod 2, (∀ i, h i ∈ U) →
        (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p 0 = 0) ∧
      ((n : ℝ) - Module.finrank (ZMod 2) U) ≤
        2 ^ (2 * j - 3) * Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) := by sorry
