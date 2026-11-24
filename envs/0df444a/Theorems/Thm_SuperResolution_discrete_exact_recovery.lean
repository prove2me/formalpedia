-- Prove2me | Theorems.Thm_SuperResolution_discrete_exact_recovery
-- name    : SuperResolution.discrete_exact_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:16:13.623541+00:00
-- url     : https://prove2.me/theorems/9fdb524d-3a34-4da4-8fc5-7794a64052eb
-- title:
--   Corollary 1.4 (as proved): exact discrete super-resolution by $\ell_1$ minimization
-- statement:
--   Let $N\in\mathbb{N}$, $f_c\ge128$, and $x\in\mathbb{C}^N$ with support $T=\{t:x_t\ne0\}\subset\{0,\dots,N-1\}$. Suppose the grid points $\{t/N:t\in T\}$ have minimum wrap-around separation
--
--   $$\min_{t\ne t'\in T}\ \frac1N\,d_N(t,t')\ \ge\ \frac{2}{f_c},\qquad d_N(t,t')=\min(|t-t'|,\,N-|t-t'|).$$
--
--   Let $y_k=\sum_{t=0}^{N-1}x_te^{-i2\pi kt/N}$ for $|k|\le f_c$. Then $x$ is the unique solution of $\min\|\tilde x\|_1$ subject to $F_n\tilde x=y$: every $\tilde x\ne x$ with the same data has $\|\tilde x\|_1>\|x\|_1$.
--
--   **Formalization Note** The paper prints the separation with the plain distance $|t-t'|/N$ and does not repeat $f_c\ge128$. The statement uses the wrap-around distance and $f_c\ge128$, which is what the derivation from Theorem 1.2 gives. With the plain distance the printed corollary is false: for $f_c=128$, $N=1024$ and $x=e_0-e_{N-1}$ the minimum $\ell_1$ norm is $0.828<2=\|x\|_1$.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 1.4, Corollary 1.4, eqs. (1.9)–(1.11), p. 7

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem discrete_exact_recovery (N fc : ℕ) (hfc : 128 ≤ fc) (x : Fin N → ℂ)
    (hsep : ENNReal.ofReal (2 / fc) ≤ minSep ((gridSupport x).image (gridPt N)))
    (x' : Fin N → ℂ) (hx' : ∀ k : ℤ, |k| ≤ fc → partialFourier x' k = partialFourier x k)
    (hne : x' ≠ x) :
    l1norm x < l1norm x' := by sorry

end SuperResolution
