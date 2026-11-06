-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_2_3
-- name    : UnobservedWelfare.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:29:56.535199+00:00
-- url     : https://prove2.me/theorems/17b79b0d-93aa-4436-a3b6-300db49f9423
-- title:
--   Lemma 2.3 — expenditure bound and logarithmic purchase support
-- statement:
--   Let $u$ be a buyer utility satisfying RC at scale $W>0$, let $p\gg0$ and $x\in D(p)$. Then
--
--   1. $p\cdot x\le W$;
--   2. for every $z\in\mathbb R^m_+$,
--   $$e^{-S(z)/W}\le e^{-S(p)/W}\,a(z;p,x),\tag{29}$$
--   with $e^{-\infty}=0$ when $S(z)=+\infty$;
--   3. the affine function $a(\cdot;p,x)$ has nonnegative constant coefficient $1-p\cdot x/W$ and nonnegative linear coefficients $x_i/W$, and is strictly positive on $\mathbb R^m_{++}$;
--   4. $x_i\le W/p_i$ for every $i$, and
--   $$S(z)-S(p)\ge-W\log a(z;p,x)\qquad(z\gg0).\tag{30}$$
--
--   RC thus bounds every buyer's spending by $W$ and lets the seller lower-bound surplus changes using only the posted price and the observed purchase.
--
--   **Formalization Note** (29) is stated as: either $S(z)=+\infty$, or $S(z)$ is finite and the real inequality holds.
--
--   Differences from the source:
--   - encoding: (29) for $z\in\mathbb R^m_+$ with the convention $e^{-\infty}=0$ → $S(z)=+\infty$, or $S(z)$ finite and the real inequality; reason: when $S(z)=+\infty$ the source inequality reads $0\le e^{-S(p)/W}a$, which is the coefficient clause
--   - encoding: "nonnegative constant and linear coefficients" → $0\le1-p\cdot x/W$ and $0\le x_i/W$ for all $i$; reason: these are the coefficients of $a(z;p,x)=(1-p\cdot x/W)+\sum_i(x_i/W)z_i$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 2.3, (29), (30), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 2.3 (expenditure bound and logarithmic purchase support)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 2.3,
p.17 (PDF p.19)). Let `u` be a buyer utility satisfying RC at scale `W > 0`. For every `p ≫ 0` and
every `x ∈ D(p)`: `p · x ≤ W`; `e^{−S(z)/W} ≤ e^{−S(p)/W} a(z; p, x)` for every `z ∈ ℝ^m_+` (29);
the affine function `a(·; p, x)` has nonnegative constant and linear coefficients and is strictly
positive on `ℝ^m_{++}`; `x_i ≤ W/p_i` for every `i`; and `S(z) − S(p) ≥ −W log a(z; p, x)` for
`z ≫ 0` (30).

**Formalization Note** In (29) the surplus `S(z)` at a boundary price may be `+∞`, where
`e^{−∞} = 0`; the clause is stated as "`S(z) = +∞`, or `S(z)` is finite and the real inequality
holds" (with `S(z) = +∞` the paper's inequality is `0 ≤ e^{−S(p)/W} a`, which is the coefficient
clause). The constant coefficient of `a(z; p, x) = (1 − p·x/W) + Σ_i (x_i/W) z_i` is
`1 − p·x/W` and the linear ones are `x_i/W`. -/
theorem lemma_2_3 {m : ℕ} (W : ℝ) (hW : 0 < W) (u : (Fin m → ℝ) → EReal)
    (hu : IsBuyerUtility u) (hRC : IsRC W u) (p : Fin m → ℝ) (hp : p ∈ posOrthant m)
    (x : Fin m → ℝ) (hx : x ∈ demand u p) :
    p ⬝ᵥ x ≤ W ∧
    (∀ z, 0 ≤ z → surplus u z = ⊤ ∨
      (surplus u z ≠ ⊥ ∧ Real.exp (-(surplus u z).toReal / W) ≤
        Real.exp (-(surplus u p).toReal / W) * affineRecord W p x z)) ∧
    (0 ≤ 1 - (p ⬝ᵥ x) / W ∧ ∀ i, 0 ≤ x i / W) ∧
    (∀ z ∈ posOrthant m, 0 < affineRecord W p x z) ∧
    (∀ i, x i ≤ W / p i) ∧
    (∀ z ∈ posOrthant m,
      (surplus u z).toReal - (surplus u p).toReal ≥ -W * Real.log (affineRecord W p x z)) := by sorry

end UnobservedWelfare
