-- Prove2me | Theorems.Thm_RobustKellyTV_corollary_2_3
-- name    : RobustKellyTV.corollary_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:29.903367+00:00
-- url     : https://prove2.me/theorems/ddd998b7-9b08-413f-a2f1-24c7b392acff
-- title:
--   Corollary 2.3 — $E_U=\arg\max_{E\in\mathcal E_0}\sum_ic_i\log E_i$ for $U=c/\sum_jc_j$
-- statement:
--   Assume the standing assumptions. For positive weights $c_1,\dots,c_d$ and $U_i=c_i/\sum_jc_j$,
--
--   $$E_U=\arg\max_{E\in\mathcal E_0}\sum_{i=1}^dc_i\log E_i ,$$
--
--   i.e. $E_U\in\mathcal E_0$ and every other $E\in\mathcal E_0$ has a strictly smaller objective.
--
--   This identifies the clipped-Kelly update as a follow-the-regularized-leader step over $\mathcal E_0$.
--
--   Differences from the source:
--   - encoding: Σ_i c_i log E_i over E ≥ 0 → the objective in EReal with log 0 = −∞ (HayashiHoeffding.elog), zero-weight terms contributing 0; reason: Lean's Real.log 0 = 0 would make factors with a zero coordinate look better than they are
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.1, Corollary 2.3, p.8

import Mathlib
import Definitions.Def_RobustKellyTV_oracleE

namespace RobustKellyTV

/-- **Corollary 2.3**. A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Corollary 2.3, p.8.

For positive weights `c₁, …, c_d` and `Uᵢ = cᵢ / Σⱼ cⱼ`, `E_U = argmax_{E ∈ E0} Σᵢ cᵢ log Eᵢ`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. The objective is in `EReal` with `log 0 = −∞`. "argmax" is the unique
maximizer: `E_U ∈ E0` and every other `E ∈ E0` has strictly smaller objective. -/
theorem corollary_2_3 {d : ℕ} (σ : Setting d) (c : Fin d → ℝ) (hc : ∀ i, 0 < c i) :
    oracleE σ (fun i => c i / ∑ j, c j) ∈ eClass σ ∧
      ∀ E ∈ eClass σ, E ≠ oracleE σ (fun i => c i / ∑ j, c j) →
        logObj c E < logObj c (oracleE σ (fun i => c i / ∑ j, c j)) := by sorry

end RobustKellyTV
