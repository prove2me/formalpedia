-- Prove2me | Theorems.Thm_SchoenfeldBRH_zero_count_upper_low_heights
-- name    : SchoenfeldBRH.zero_count_upper_low_heights
-- status  : Open
-- author  : @xuanji
-- created : 2026-11-24T02:20:06.566077+00:00
-- url     : https://prove2.me/theorems/ac6ee131-7e87-4c57-8ffc-a83695b76d6f
-- title:
--   Upper bound $N(t)\le \frac{t}{2\pi}(\log\frac{t}{2\pi}-1)+\frac52$ for $14\le t\le 2500$
-- statement:
--   Let $N(t)$ be the number of nontrivial zeros $\rho$ of the Riemann zeta function with $0<\operatorname{Im}\rho\le t$, counted with multiplicity (`DusartSmoothing.RvM.Ncount 0 t`, the finite sum of the analytic orders of $\zeta$ over zeros in the critical strip with $0<\operatorname{Im}\rho\le t$). Then
--   $$N(t)\le \frac{t}{2\pi}\Bigl(\log\frac{t}{2\pi}-1\Bigr)+\frac52\qquad\text{for all }14\le t\le 2500.$$
--
--   By the Riemann–von Mangoldt formula $N(t)=\frac{t}{2\pi}(\log\frac{t}{2\pi}-1)+\frac78+S(t)+O(1/t)$, and $|S(t)|<1.7$ in this range; the claim follows from the known exact counts of zeros up to height $2500$ (there are $1985$ of them, all simple and on the critical line). Numerically the largest value of $N(t)-\frac{t}{2\pi}(\log\frac{t}{2\pi}-1)$ on $[14,2500]$ is about $2.13$.
-- source:
--   J. B. Rosser, J. M. Yohe, L. Schoenfeld, Rigorous computation and the zeros of the Riemann zeta-function, Proc. IFIP Congress 1968; A. M. Odlyzko, tables of zeros of the Riemann zeta function; Riemann–von Mangoldt formula (Titchmarsh, The Theory of the Riemann Zeta-Function, §9.3).

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_CompletedZeta

theorem SchoenfeldBRH.zero_count_upper_low_heights :
    ∀ t : ℝ, 14 ≤ t → t ≤ 2500 →
      (DusartSmoothing.RvM.Ncount 0 t : ℝ) ≤
        t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2 := by sorry
