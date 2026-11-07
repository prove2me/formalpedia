-- Prove2me | Theorems.Thm_PNormReg_eq_13_14
-- name    : PNormReg.eq_13_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:39:55.119699+00:00
-- url     : https://prove2.me/theorems/716a9f7c-6979-4531-97ba-1edddc8ec6d8
-- title:
--   (13)–(14), p.19 — $(f(x)-f^\star)/(16p)\le\mathrm{res}^\star_p\le f(x)-f^\star$ and $\mathrm{res}_p(\Delta)\le f(x)-f(x-\Delta/p)$
-- statement:
--   Fix a problem (11) with $p\ge2$ and a feasible point $x$. Then $f^\star$ and $\mathrm{res}^\star_p$ are attained, and
--
--   $$\frac{f(x)-f^\star}{16p}\le\mathrm{res}^\star_p\le f(x)-f^\star,$$
--
--   and for every $\Delta$ with $C\Delta=0$,
--
--   $$\mathrm{res}_p(\Delta)\le f(x)-f(x-\Delta/p).$$
--
--   The first display says the optimal residual value is within an $O(p)$ factor of the current objective gap; the second translates residual value into decrease of $f$. Together they justify iterative refinement.
--
--   Differences from the source:
--   - encoding: the max and min of (11), (12) → IsLeast and IsGreatest clauses for the sInf and sSup defining f⋆ and res⋆_p; reason: they make the two optima the printed min and max; both exist because N has full column rank and p ≥ 2
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), §3, eqs. (13)–(14), p.19 (PDF p.20)

import Mathlib
import Definitions.Def_PNormReg_Regression

open Matrix

namespace PNormReg

/-- **(13)–(14)**, §3, p.19 (PDF p.20).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

For feasible `x`: `f⋆` and `res⋆_p` are attained; `(f(x) − f⋆)/(16p) ≤ res⋆_p ≤ f(x) − f⋆`; and for every
`∆` with `C∆ = 0`, `res_p(∆) ≤ f(x) − f(x − ∆/p)`.

**Formalization Note.** Attainment is stated as `IsLeast` and `IsGreatest`, so the `sInf`/`sSup` of
`fStar`/`resStar` are the printed min and max. The page presents (13)–(14) as a consequence of
[AKPS24, Lemma 2.6]. -/
theorem eq_13_14 {n d m : ℕ} (G : GenRegression n d m) (hG : G.IsStanding) (p : ℝ) (hp : 2 ≤ p)
    (x : Fin d → ℝ) (hx : G.Feasible x) :
    IsLeast (G.obj p '' {y | G.Feasible y}) (G.fStar p) ∧
    IsGreatest (G.res p x '' {Δ | G.C *ᵥ Δ = 0}) (G.resStar p x) ∧
    (G.obj p x - G.fStar p) / (16 * p) ≤ G.resStar p x ∧
    G.resStar p x ≤ G.obj p x - G.fStar p ∧
    ∀ Δ : Fin d → ℝ, G.C *ᵥ Δ = 0 →
      G.res p x Δ ≤ G.obj p x - G.obj p (x - (1 / p) • Δ) := by sorry

end PNormReg
