-- Prove2me | Theorems.Thm_SpectrumLB_eq_7_14
-- name    : SpectrumLB.eq_7_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:37.13297+00:00
-- url     : https://prove2.me/theorems/09df152f-c750-44df-9bb7-ff699815a326
-- title:
--   Eq. (7.14) — concentration of Lipschitz functions of $K$ independent Haar unitaries
-- statement:
--   Let $F:U(d)^K\to\mathbb R$ be $\Lambda$-Lipschitz, $\Lambda>0$, with respect to the $L_2$-sum of Hilbert–Schmidt metrics:
--
--   $$
--   |F(U_1,\dots,U_K)-F(U_1',\dots,U_K')|\ \le\ \Lambda\sqrt{\sum_{i=1}^K\|U_i-U_i'\|_2^2}\qquad\text{for all }(U_i),(U_i'),
--   $$
--
--   where $\|A\|_2^2=\sum_{x,y}|A_{xy}|^2$. If $U_1,\dots,U_K$ are independent Haar-random unitaries, then for every $u\ge0$,
--
--   $$
--   \Pr\Big(\big|F(U_1,\dots,U_K)-\mathbf EF(U_1,\dots,U_K)\big|\ge u\Big)\ \le\ 2\,e^{-(d-2)u^2/(24\Lambda^2)} .
--   $$
--
--   This is the concentration-of-measure input of the spectral separation (Lemma 7.3). The paper imports it from Meckes, *The Random Matrix Theory of the Classical Compact Groups*, Theorem 5.17, and does not prove it.
--
--   Differences from the source:
--   - encoding: ‖·‖₂ Hilbert–Schmidt norm and the L2-sum metric → √(Σ_i Σ_{x,y} |(U_i)_{xy} − (U'_i)_{xy}|²) written out; reason: the same metric
--   - encoding: u (implicitly positive), Λ-Lipschitz → u ≥ 0, Λ > 0; reason: at u = 0 the bound is trivial; Λ appears in a denominator
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §7.2, Eqs. (7.13)–(7.14), p. 36 (citing [Mec19, Theorem 5.17])

import Mathlib
import Definitions.Def_SpectrumLB_haarK

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Eq. (7.14) (concentration of Lipschitz functions of Haar unitaries).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §7.2, Eqs. (7.13)–(7.14), p. 36: "Let F : U(d)^{×K} → R be a real function that is Λ-Lipschitz with
respect to the L2-sum of Hilbert–Schmidt metrics on U(d) … By a standard result on the concentration of
Lipschitz functions of independent Haar-random unitaries, see e.g. [Mec19, Theorem 5.17], we have
Pr(|F(U_1, ⋯, U_K) − E F(U_1, ⋯, U_K)| ≥ u) ≤ 2e^{−(d−2)u^2/(24Λ^2)}."

**Formalization Note.** The metric of (7.13) is written out: `√(Σ_i ‖U_i − U'_i‖_2^2)` with the
Hilbert–Schmidt (Frobenius) norm `‖A‖_2^2 = Σ_{x,y} |A_{xy}|^2`. `Λ > 0` and `u ≥ 0`. The paper imports this
from [Mec19] and does not prove it; it is a milestone so that the goal is unconditional. -/
theorem eq_7_14 (d K : ℕ) (Λ : ℝ) (hΛ : 0 < Λ)
    (F : (Fin K → Matrix.unitaryGroup (Fin d) ℂ) → ℝ)
    (hF : ∀ U V : Fin K → Matrix.unitaryGroup (Fin d) ℂ,
      |F U - F V| ≤ Λ * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin d) (Fin d) ℂ) x y - (V i : Matrix (Fin d) (Fin d) ℂ) x y‖ ^ 2))
    (u : ℝ) (hu : 0 ≤ u) :
    haarK d K {U | u ≤ |F U - ∫ V, F V ∂haarK d K|} ≤
      ENNReal.ofReal (2 * Real.exp (-(((d : ℝ) - 2) * u ^ 2) / (24 * Λ ^ 2))) := by sorry

end SpectrumLB
