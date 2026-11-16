-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_rank_lower_bound
-- name    : QuantumFunctionalEstimation.Master.Supplement.rank_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:12:49.237743+00:00
-- url     : https://prove2.me/theorems/99aea937-6286-4475-ad7e-8e4e1ea653dd
-- title:
--   Theorem 5.22 — two-sided rank-testing lower bound
-- statement:
--   Consider a two-sided tester, successful with probability at least $2/3$, for $\operatorname{rank}(\rho)\le r$ versus $\Delta_r(\rho)\ge\varepsilon$. Every copy budget $N$ sufficient in every positive finite ambient dimension satisfies
--   $$N\ge k\frac{r^2}{\varepsilon\log^2r\max\{1,\varepsilon\log^2r\}}.$$
--
--   There exist universal $k>0$, $\varepsilon_0\in(0,1/2]$ and $r_0\ge2$, chosen before every $r\ge r_0$ and $0<\varepsilon\le\varepsilon_0$. There is no one-sided-error restriction and no requirement in the promise gap.
--
--   This companion application retains the full error transition and treats ambient dimension in the worst-case sense.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
--   - encoding: copy complexity without a fixed ambient dimension → one copy budget admitting successful testers in every positive finite ambient dimension; reason: expresses the worst-case complexity and avoids a false bound in trivial local spaces
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 35 (PDF p. 37), Theorem 5.22; alias Theorem 1.9, printed p. 7 (PDF p. 9)

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Theorem 5.22, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem rank_lower_bound :
  ∃ k ε₀ : ℝ, 0 < k ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
  ∃ r₀ : ℕ, 2 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ N : ℕ, (∀ d : ℕ, 0 < d →
      ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin d) Bool,
        RankSuccessful d r N ε E) → k * transitionRate r ε ≤ N := by sorry

end QuantumFunctionalEstimation.Master.Supplement
