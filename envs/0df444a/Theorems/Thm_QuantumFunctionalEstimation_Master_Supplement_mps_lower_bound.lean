-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_mps_lower_bound
-- name    : QuantumFunctionalEstimation.Master.Supplement.mps_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:14:25.849404+00:00
-- url     : https://prove2.me/theorems/87383c35-4e6e-4227-90e2-8bc46410fbcc
-- title:
--   Theorem 5.24 — matrix product state testing lower bound
-- statement:
--   Consider a two-sided tester, successful with probability at least $2/3$, for open-boundary MPS of bond dimension at most $r$ versus pure-projector trace distance at least $\varepsilon$ from every such normalized MPS. Every copy budget $N$ sufficient in every positive finite ambient dimension satisfies
--   $$N\ge k\frac{nr^2}{\varepsilon^2\log^2(nr)}.$$
--
--   There exist universal $C,c,k>0$ and integers $n_0,r_0\ge2$, chosen before all $n\ge n_0$, $r\ge r_0$ and $0<\varepsilon\le1/2$, subject to $r\ge C\log n$ and $\varepsilon^2\log^2(nr)\le cn$. All positive finite site dimensions, including varying dimensions, are allowed; odd $n$ is included.
--
--   This companion application retains the full error transition and treats ambient dimension in the worst-case sense.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
--   - encoding: copy complexity without a fixed ambient dimension → one copy budget admitting successful testers in every positive finite ambient dimension; reason: expresses the worst-case complexity and avoids a false bound in trivial local spaces
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 36 (PDF p. 38), Theorem 5.24; alias Theorem 1.11, printed p. 8 (PDF p. 10)

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Theorem 5.24, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem mps_lower_bound :
  ∃ C c k : ℝ, 0 < C ∧ 0 < c ∧ 0 < k ∧
  ∃ n₀ r₀ : ℕ, 2 ≤ n₀ ∧ 2 ≤ r₀ ∧ ∀ n r : ℕ, n₀ ≤ n → r₀ ≤ r →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → C * Real.log n ≤ r →
      ε^2 * Real.log ((n : ℝ) * r)^2 ≤ c * n →
    ∀ N : ℕ, (∀ dims : Fin n → ℕ, (∀ i, 0 < dims i) →
      ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Sites dims) Bool,
        MPSSuccessful dims r N ε E) →
      k * (n : ℝ) * (r : ℝ)^2 / (ε^2 * Real.log ((n : ℝ) * r)^2) ≤ N := by sorry

end QuantumFunctionalEstimation.Master.Supplement
