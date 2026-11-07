-- Prove2me | Theorems.Thm_RobustKellyTV_theorem_2_2
-- name    : RobustKellyTV.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:36.458428+00:00
-- url     : https://prove2.me/theorems/243eddd2-7239-4041-a37c-a68b5a9e6b01
-- title:
--   Theorem 2.2 — reverse projection $R_U$ and the pointwise Kelly oracle $E_U$
-- statement:
--   Assume the standing assumptions and let $U\in\Delta_d^\circ$. Then:
--
--   1. $R_U\in\mathcal P_0$ and $E_U\in\mathcal E_0$;
--   2. $R_U$ is the unique reverse information projection of $U$ onto $\mathcal P_0$: for every $R\in\mathcal P_0$ with $R\ne R_U$, $D_{\mathrm{KL}}(U\|R_U)<D_{\mathrm{KL}}(U\|R)$;
--   3. $\Gamma(U)=D_{\mathrm{KL}}(U\|R_U)=\inf_{R\in\mathcal P_0}D_{\mathrm{KL}}(U\|R)$, $E_U=U/R_U$ coordinatewise, the value of (9) at $E_U$ is $\Gamma(U)$, and $E_U$ is the unique maximizer of
--   $$E\mapsto\sum_{i=1}^dU_i\log E_i\quad\text{over }E\in\mathcal E_0 .$$
--
--   For $U\in\mathcal P_0$ the conventions $E_U\equiv1$, $R_U=U$, $\Gamma(U)=0$ apply. The theorem identifies the log-optimal null-valid bet as a clipped likelihood ratio.
--
--   Differences from the source:
--   - encoding: Σ_i c_i log E_i over E ≥ 0 → the objective in EReal with log 0 = −∞ (HayashiHoeffding.elog), zero-weight terms contributing 0; reason: Lean's Real.log 0 = 0 would make factors with a zero coordinate look better than they are
--   - reading: R_U is the unique reverse information projection (RIPr) and R_U = argmin_{R∈P0} D_KL(U‖R) → R_U ∈ P0 and every other R ∈ P0 has strictly larger D_KL(U‖R); reason: RIPr means the KL minimizer over P0 (p.7, p.22); uniqueness is the strict inequality
--   - encoding: E_U is the unique maximizer in (9) → E_U ∈ E0, its objective equals Γ(U), and every other E ∈ E0 has strictly smaller objective; reason: the unique-argmax statement together with the value (9)
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.1, Theorem 2.2, p.7 (proof pp.21–22)

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_oracleE

namespace RobustKellyTV

/-- **Theorem 2.2** (Reverse projection and pointwise Kelly oracle). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Theorem 2.2, p.7.

Let `U ∈ ∆°_d`. Then (a) `R_U ∈ P0` and `E_U ∈ E0`; (b) `R_U` is the unique reverse information
projection and `R_U = argmin_{R ∈ P0} D_KL(U‖R)`; (c) `Γ(U) = D_KL(U‖R_U) = inf_{R ∈ P0} D_KL(U‖R)`,
and `E_U = U / R_U` is the unique maximizer in (9).

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. Stated for every interior `U`, including `U ∈ P0`, where the
convention `E_U ≡ 1`, `R_U = U` of p.7 applies. The reverse information projection is the
minimizer of `R ↦ D_KL(U‖R)` over `P0`; "unique minimizer" is: `R_U ∈ P0` and every other `R ∈ P0`
has strictly larger divergence. The objective of (9) is `Σᵢ Uᵢ log Eᵢ` in `EReal` with `log 0 = −∞`;
"unique maximizer" is: `E_U ∈ E0`, its objective equals `Γ(U)` (the value (9)), and every other
`E ∈ E0` has strictly smaller objective. -/
theorem theorem_2_2 {d : ℕ} (σ : Setting d) (U : Fin d → ℝ) (hU : U ∈ interiorSimplex d) :
    (oracleR σ U ∈ nullBall σ ∧ oracleE σ U ∈ eClass σ) ∧
      (∀ R ∈ nullBall σ, R ≠ oracleR σ U → kl U (oracleR σ U) < kl U R) ∧
      (Gamma σ U = (kl U (oracleR σ U)).toReal ∧
        kl U (oracleR σ U) = ⨅ R ∈ nullBall σ, kl U R ∧
        (∀ i, oracleE σ U i = U i / oracleR σ U i) ∧
        logObj U (oracleE σ U) = (Gamma σ U : EReal) ∧
        ∀ E ∈ eClass σ, E ≠ oracleE σ U → logObj U E < logObj U (oracleE σ U)) := by sorry

end RobustKellyTV
