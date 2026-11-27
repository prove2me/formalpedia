-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_quadratic_spectral_norm_sq
-- name    : ParityDegreeDepth.Core.quadratic_spectral_norm_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:37.457496+00:00
-- url     : https://prove2.me/theorems/427e3a2e-5015-56df-ab4b-4d8e0afc4881
-- title:
--   Quadratic phases: $\|\widehat{(-1)^q}\|_1^2 = 2^{\operatorname{rank}\beta_q}$
-- statement:
--   Let $q:\mathbb F_2^n\to\mathbb F_2$ have degree at most $2$, in the sense that all third finite differences vanish:
--
--   $$
--   \sum_{\varepsilon\in\{0,1\}^3} q(x+\varepsilon_1u+\varepsilon_2v+\varepsilon_3w)=0\qquad\text{for all }x,u,v,w .
--   $$
--
--   Let $\beta_q(u,v)=q(u+v)+q(u)+q(v)+q(0)$ be its polar form and $B=\big(\beta_q(e_a,e_b)\big)_{a,b}$ its Gram matrix over $\mathbb F_2$. Then the sign function $g=(-1)^q$ satisfies
--
--   $$
--   \|\widehat g\|_1^{\,2}=\Big(\sum_{\xi\in\mathbb F_2^n}|\widehat g(\xi)|\Big)^2 = 2^{\operatorname{rank}_{\mathbb F_2} B},
--   $$
--
--   where $\widehat g(\xi)=2^{-n}\sum_x g(x)(-1)^{\xi\cdot x}$. With polar rank $2r$ this is $\|\widehat g\|_1=2^r$, the spectral-norm clause of Lemma 2.6. It converts contraction ranks into spectral norms in Lemma 3.2 and controls the quadratic base case of the recursion.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §2, Lemma 2.6 (s(f)=2^{2r}, |f^(xi)| in {0,2^{-r}}, ||f^||_1 = 2^r) and Appendix A.5, pp. 5, 20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

theorem ParityDegreeDepth.Core.quadratic_spectral_norm_sq {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2)
    (hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0) :
    (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (q x).val) ξ|) ^ 2 =
      2 ^ (Matrix.of fun a b : Fin n =>
        q (Pi.single a 1 + Pi.single b 1) + q (Pi.single a 1) + q (Pi.single b 1) + q 0).rank := by sorry
