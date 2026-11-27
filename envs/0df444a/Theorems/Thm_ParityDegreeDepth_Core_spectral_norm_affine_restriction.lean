-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_spectral_norm_affine_restriction
-- name    : ParityDegreeDepth.Core.spectral_norm_affine_restriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:37.180996+00:00
-- url     : https://prove2.me/theorems/e8724352-f57f-52b8-89aa-3b8dc31de10b
-- title:
--   Lemma 2.2: affine restriction does not increase the spectral norm
-- statement:
--   Let $f:\mathbb F_2^n\to\mathbb R$, let $B:\mathbb F_2^m\to\mathbb F_2^n$ be $\mathbb F_2$-linear and $a\in\mathbb F_2^n$. Then the restriction of $f$ to the affine subspace $a+B(\mathbb F_2^m)$, written in the coordinates $y\mapsto a+By$, satisfies
--
--   $$
--   \sum_{\eta\in\mathbb F_2^m}\big|\widehat{f(a+B\,\cdot)}(\eta)\big|\;\le\;\sum_{\xi\in\mathbb F_2^n}|\widehat f(\xi)| .
--   $$
--
--   This is the spectral-norm clause of Lemma 2.2: each coefficient of the restriction is a signed sum of a disjoint group of coefficients of $f$. It allows every branch of the recursion to pay with the spectral norm of the original function.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §2, Lemma 2.2 and its proof in Appendix A.2, pp. 4, 17-18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

theorem ParityDegreeDepth.Core.spectral_norm_affine_restriction {n m : ℕ}
    (f : (Fin n → ZMod 2) → ℝ) (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) :
    ∑ ξ, |QAlgorithms.boolFourier (fun y => f (a + B y)) ξ| ≤ ∑ ξ, |QAlgorithms.boolFourier f ξ| := by sorry
