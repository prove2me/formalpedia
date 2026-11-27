-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_quadratic_vanishing_codim
-- name    : ParityDegreeDepth.Core.quadratic_vanishing_codim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:38.756819+00:00
-- url     : https://prove2.me/theorems/3b52f1c6-5102-4fe0-a03c-3cdf0595ad09
-- title:
--   Quadratic case: a vanishing subspace of codimension $\le \log_2\|\widehat f\|_1$
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have degree at most $2$ (all third finite differences vanish) and $f=(-1)^p$. Then there is a subspace $U\le\mathbb F_2^n$ on which the polar form vanishes,
--
--   $$
--   \Delta_u\Delta_v p(0)=p(u+v)+p(u)+p(v)+p(0)=0\qquad(u,v\in U),
--   $$
--
--   and whose codimension satisfies
--
--   $$
--   n-\dim U\;\le\;\log_2\|\widehat f\|_1 .
--   $$
--
--   Querying a basis of $U^\perp$ therefore makes $p$ affine on every branch, which (with one more query) gives the quadratic bound $D_\oplus(f)\le 1+r=1+\log_2\|\widehat f\|_1$ of Lemma 2.6 used as $\Gamma(2)$ in the proof of Theorem 1.3.
--
--   **Formalization Note** Differences are written as the left fold `(List.ofFn h).foldl (fun q v y => q (y + v) + q y) p`, i.e. $\Delta_{h_1}\cdots\Delta_{h_k}p$.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §2 Lemma 2.6 (D(f) <= r+1 via Dickson coordinates, eq. (6)), Appendix A.5 Proposition A.6, and the quadratic step in the proof of Theorem 1.3 (§3.6), pp. 5, 11, 20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

theorem ParityDegreeDepth.Core.quadratic_vanishing_codim {n : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (hp : ∀ (h : Fin 3 → Fin n → ZMod 2) (x : Fin n → ZMod 2),
      (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p x = 0) :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ h : Fin 2 → Fin n → ZMod 2, (∀ i, h i ∈ U) →
        (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p 0 = 0) ∧
      ((n : ℝ) - Module.finrank (ZMod 2) U) ≤
        Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) := by sorry
