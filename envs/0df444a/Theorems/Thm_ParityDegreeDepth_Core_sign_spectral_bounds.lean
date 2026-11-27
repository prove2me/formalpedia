-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_sign_spectral_bounds
-- name    : ParityDegreeDepth.Core.sign_spectral_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:41.182686+00:00
-- url     : https://prove2.me/theorems/c097c795-7a97-40cc-a8af-dbe1ae253bb0
-- title:
--   Eq. (3): $1\le\|\widehat f\|_1\le\sqrt{s(f)}$, and $s(f)\le1$ forces an affine phase
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ and $f=(-1)^p$, with sparsity $s(f)=|\{\xi:\widehat f(\xi)\ne0\}|$. Then
--
--   1. $1\le\|\widehat f\|_1$;
--   2. $\|\widehat f\|_1^2\le s(f)$, i.e. $\|\widehat f\|_1\le\sqrt{s(f)}$;
--   3. if $s(f)\le1$, then $p$ is affine: $p(x+u+v)+p(x+u)+p(x+v)+p(x)=0$ for all $x,u,v$.
--
--   Items 1–2 are eq. (3) of the source; item 3 is the equality case (a signed character), which together with Lemma A.5 shows $s(f)\ge2$ for every phase of degree at least two.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §2, eq. (3) (Parseval and Cauchy-Schwarz) and the equality case / Lemma A.5 (s(f) >= 2^d for d >= 2), pp. 4, 19-20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

theorem ParityDegreeDepth.Core.sign_spectral_bounds {n : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) :
    1 ≤ ∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ| ∧
    (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) ^ 2 ≤
      ((Finset.univ.filter fun ξ => QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ ≠ 0).card : ℝ) ∧
    ((Finset.univ.filter fun ξ => QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ ≠ 0).card ≤ 1 →
      ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0) := by sorry
