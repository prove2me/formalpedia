-- Prove2me | Theorems.Thm_PriceRobust_Stability_theorem_3
-- name    : PriceRobust.Stability.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:13.309056+00:00
-- url     : https://prove2.me/theorems/5ffb552e-4745-47ea-8244-33f511b76037
-- title:
--   Theorem 3 (a)–(b), p. 15 — robust best responses contract in some norm and their iterates converge geometrically to the special equilibrium (p*|w)
-- statement:
--   Consider the market of §3: products partitioned among firms, affine demands $q(p)=a-Rp$ with $a\ge 0$, and $R$ satisfying (P) positive definiteness ($x^\top Rx>0$ for $x\ne 0$), (Z) non-positive off-diagonal entries, and (IS) intra-firm symmetry. Fix a cost vector $w\in\mathbb R^{\mathcal N}_{++}$, let $w'=\Theta(w)$ solve the cost-projection LCP (12)–(14), and let $(p^*|w)=w'+[R+T(R)]^{-1}(a-Rw')$ be the special equilibrium. Let $RB$ be the robust best-response map. Then there exist a norm $\|\cdot\|$ on $\mathbb R^{\mathcal N}$ and a constant $0<\gamma<1$ such that:
--
--   1. (a) $RB$ is a contraction on the nonnegative orthant:
--   $$\|RB(\hat p)-RB(\tilde p)\|\le\gamma\,\|\hat p-\tilde p\|\qquad\text{for all }\hat p,\tilde p\in\mathbb R^{\mathcal N}_+;$$
--   2. (b) for every $p\in\mathbb R^{\mathcal N}_+$,
--   $$\|RB^{(n)}(p)-(p^*|w)\|\le\gamma^n\,\|p-(p^*|w)\|\quad\text{for all }n,\qquad \lim_{n\to\infty}RB^{(n)}(p)=(p^*|w).$$
--
--   In other words, the special equilibrium is globally stable under robust best responses, and convergence is geometric. This holds even though the full price game need not be supermodular and may have many Nash equilibria.
--
--   **Formalization Note** "There exists a norm" is a seminorm on $\mathbb R^{\mathcal N}$ that vanishes only at $0$; the same norm and $\gamma$ serve (a) and (b). $RB$ is the relation "$q$ is a robust best response to $p$"; part (b) is stated for every sequence $p^0\ge 0$, $p^{n+1}=RB(p^n)$, which by Lemma 1 is the unique orbit $RB^{(n)}(p^0)$. The limit is in the product topology of $\mathbb R^{\mathcal N}$. $(p^*|w)$ is expressed through any solution $w'$ of the LCP (12)–(14), which exists and is unique.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), p. 15 (PDF 16), Theorem 3

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem theorem_3 {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (w' : ι → ℝ) (hw' : M.IsCostProjection w w') :
    ∃ ν : Seminorm ℝ (ι → ℝ), (∀ x, ν x = 0 → x = 0) ∧
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
      (∀ phat ptil qhat qtil : ι → ℝ, 0 ≤ phat → 0 ≤ ptil →
        M.IsRobustBR w phat qhat → M.IsRobustBR w ptil qtil →
        ν (qhat - qtil) ≤ γ * ν (phat - ptil)) ∧
      (∀ s : ℕ → ι → ℝ, 0 ≤ s 0 → (∀ n, M.IsRobustBR w (s n) (s (n + 1))) →
        (∀ n, ν (s n - M.pstar w') ≤ γ ^ n * ν (s 0 - M.pstar w')) ∧
        Filter.Tendsto s Filter.atTop (nhds (M.pstar w'))) := by sorry

end PriceRobust.Stability
