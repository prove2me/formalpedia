-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_repeatable_outputs_can_correlate
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.repeatable_outputs_can_correlate
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:42:50.008564+00:00
-- url     : https://prove2.me/theorems/117584ec-f5a1-4358-92e8-a46bc0dd53e2
-- title:
--   Repeatable devices can correlate product-input outputs
-- statement:
--   There is a two-dimensional memory device initialized in $I_2/2$, with the fixed interaction $|0\rangle\langle0|\otimes I_2+|1\rangle\langle1|\otimes Z$, where $Z=\operatorname{diag}(1,-1)$. It repeatably implements the channel $\mathcal E(X)=(X+ZXZ)/2$ on every individual output for all product-input histories. For two independent inputs $|+\rangle\langle+|$, where $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$, the actual joint output is
--
--   $$\omega_{12}=\tfrac12|++\rangle\langle++|+\tfrac12|--\rangle\langle--|\ne\mathcal E(|+\rangle\langle+|)\otimes\mathcal E(|+\rangle\langle+|).$$
--
--   Each marginal is $I_2/2$. The same fair memory bit controls both uses without resetting.
--
--   This witnesses the source's existential observation that repeatability permits correlated outputs. The explicit witness instantiates the controlled-unitary construction of Section III; no adaptive-testing claim is made.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 5, Section IV, output correlations paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section IV, PDF p.5: an explicit repeatable shared fair I/Z device correlates two
independent plus inputs. This witnesses "may"; no assertion about adaptive measurements
or complete process distance is made. -/
theorem repeatable_outputs_can_correlate :
    ∃ D : MemoryDevice 2 2,
      D.initial = totalMixture 2 ∧
      (D.unitary : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = sharedControlledZ ∧
      Repeatable D dephasingChannel ∧
      IsChannel dephasingChannel ∧
      IsDensityMatrix (signDensity false) ∧
      twoOutputState D (signDensity false) (signDensity false) = correlatedSigns ∧
      correlatedSigns ≠ Matrix.kronecker (dephasingChannel (signDensity false))
        (dephasingChannel (signDensity false)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
