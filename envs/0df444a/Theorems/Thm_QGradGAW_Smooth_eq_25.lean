-- Prove2me | Theorems.Thm_QGradGAW_Smooth_eq_25
-- name    : QGradGAW.Smooth.eq_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:05.74215+00:00
-- url     : https://prove2.me/theorems/8efc940a-8fe2-421c-8577-556e260fab7f
-- title:
--   (25), proof of Theorem 25, p. 30 — Σ_{ℓ=−m}^{m} ⌈|a_ℓ^(2m)| S⌉ ≤ 2m + S(2 log(m) + 2) fractional queries per oracle call
-- statement:
--   For every integer $m\ge1$ and every $S\ge0$,
--   $$\sum_{\ell=-m}^{m}\Big\lceil\big|a_\ell^{(2m)}\big|\,S\Big\rceil\;\le\;2m+S\sum_{\ell=-m}^{m}\big|a_\ell^{(2m)}\big|\;\le\;2m+S\,(2\ln m+2).$$
--
--   The left-hand side is the number of fractional phase queries to $O_f$ needed to implement one call of the oracle $O^S_{g_{(2m)}}:|y\rangle\mapsto e^{iS\sum_\ell a_\ell^{(2m)}g(\ell y)}|y\rangle$, since a phase $S|a_\ell^{(2m)}|$ costs $\lceil S|a_\ell^{(2m)}|\rceil$ queries $O_f^s$ with $|s|\le1$.
--
--   **Formalization Note** The page prints the middle sum without absolute values, $S\sum_\ell a_\ell^{(2m)}$ (which is $0$ since $a_{-\ell}^{(2m)}=-a_\ell^{(2m)}$); the statement uses $|a_\ell^{(2m)}|$, which is what the bound (24) is about. "log" is the natural logarithm, as in (24).
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 30, proof of Theorem 25, display (25)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

/-- arXiv:1711.00465v3, p. 30, display (25) in the proof of Theorem 25: for `m ∈ ℕ₊` and
`S ≥ 0`, the number of fractional phase queries `Σ_{ℓ=−m}^{m} ⌈|a_ℓ^(2m)| S⌉` satisfies
`Σ_ℓ ⌈|a_ℓ^(2m)| S⌉ ≤ 2m + S Σ_ℓ |a_ℓ^(2m)| ≤ 2m + S(2 log(m) + 2)` (natural logarithm; the page
prints the middle sum without the absolute values). -/
theorem eq_25 (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 0 ≤ S) :
    (∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, (⌈|centralCoeff m ℓ| * S⌉₊ : ℝ)) ≤
        2 * m + S * ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ| ∧
      2 * m + S * ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ| ≤
        2 * m + S * (2 * Real.log m + 2) := by sorry

end QGradGAW.Smooth
