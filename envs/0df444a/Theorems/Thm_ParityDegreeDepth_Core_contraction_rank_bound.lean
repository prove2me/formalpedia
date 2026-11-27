-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_contraction_rank_bound
-- name    : ParityDegreeDepth.Core.contraction_rank_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:41.430586+00:00
-- url     : https://prove2.me/theorems/d1a9fbcf-ad57-4534-aab6-db173af16b74
-- title:
--   Lemma 3.2: binary contraction ranks $\le 2^{d-1}\log_2\|\widehat f\|_1$
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have degree at most $d=k+2$ (all $(d+1)$-fold finite differences vanish), let $f=(-1)^p$ and let $T=\Delta^d p$ be its top form, $T(h_1,\dots,h_d)=\Delta_{h_1}\cdots\Delta_{h_d}p(0)$. For any binary anchors $h_1,\dots,h_k\in\mathbb F_2^n$, the contraction matrix $\big(T(h_1,\dots,h_k,e_a,e_b)\big)_{a,b}$ satisfies
--
--   $$
--   \operatorname{rank}_{\mathbb F_2} T(h_1,\dots,h_k,-,-)\;\le\;2^{k+1}\log_2\|\widehat f\|_1=2^{d-1}\log_2\|\widehat f\|_1 .
--   $$
--
--   Maximising over the anchors gives $M(T)\le 2^{d-1}\log_2\|\widehat f\|_1$, Lemma 3.2 of the source (Step 1 of the main argument).
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §3.2, Lemma 3.2 and its proof (eq. (8), Lemmas 2.5, 2.6), pp. 5-6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

theorem ParityDegreeDepth.Core.contraction_rank_bound {n k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (hp : ∀ (h : Fin (k + 2 + 1) → Fin n → ZMod 2) (x : Fin n → ZMod 2),
      (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p x = 0)
    (h : Fin k → Fin n → ZMod 2) :
    ((Matrix.of fun a b : Fin n => (List.ofFn (Fin.append h ![Pi.single a 1, Pi.single b 1])).foldl
        (fun q v y => q (y + v) + q y) p 0).rank : ℝ) ≤
      2 ^ (k + 1) * Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) := by sorry
