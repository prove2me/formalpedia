-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_totalMixture_reset_repeatable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.totalMixture_reset_repeatable
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:41:53.606232+00:00
-- url     : https://prove2.me/theorems/7836b5ce-84fa-4d1b-9a54-f2e155cc78a1
-- title:
--   Completely mixing reset is random unitary and repeatable
-- statement:
--   Let $d\ge1$ and define the completely mixing channel on all operators on $\mathbb C^d$ by
--
--   $$\mathcal A(X)=\operatorname{Tr}(X)\frac{I_d}{d}.$$
--
--   Then $\mathcal A$ is a finite random-unitary channel and has a finite-memory repeatable implementation: one fixed unitary and a normalized memory initializer implement its individual output marginals for every product-input history at every horizon, without reset or an extra environment. On normalized states the output is $I_d/d$.
--
--   This supplies a repeatable reset to the total mixture within the paper's marginal model.
--
--   **Formalization Note** The map is the accepted depolarizing map at parameter $1$.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 4, Section IV, reset paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section IV, PDF p.4: the completely mixing reset is random unitary and repeatable.
The accepted depolarizing map at p=1 is its trace-weighted linear extension to operators. -/
theorem totalMixture_reset_repeatable (d : ℕ) (hd : 0 < d) :
    IsRandomUnitary (QuditFidelity.depolarizingMap d hd 1) ∧
      HasFiniteRepeatableImplementation (QuditFidelity.depolarizingMap d hd 1) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
