-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_normalizedKrausBranches
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.normalizedKrausBranches
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:19:43.738527+00:00
-- url     : https://prove2.me/theorems/e1048720-22f5-438e-8d05-feba5696d0e4
-- title:
--   Selecting normalized Kraus branches
-- statement:
--   Let $\rho$ be a density operator on a nonzero finite-dimensional space $S$, let $\mathcal A:\mathcal B(C)\to\mathcal B(S)$ be CP and trace preserving, and let $\mathcal E:\mathcal B(S)\to\mathcal B(C)$ be CP with $\operatorname{tr}\mathcal E(\rho)=1$. There are nonempty finite Kraus representations $\{A_i\}$ and $\{E_j\}$ with a distinguished branch of probability $p=\operatorname{tr}(E_1\rho E_1^\dagger)>0$ such that
--
--   $$F_e(\rho,\mathcal A\mathcal E)\leq\left|\operatorname{tr}\left(A_1\frac{E_1}{\sqrt p}\rho\right)\right|^2.$$
--
--   The operator normalization is $1/\sqrt p$, corresponding to $1/p$ for its CP operation.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 10, Lemma 10; Eqs.(95)–(96)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.10, Lemma 10: selected branch has positive probability, and the OPERATOR
is divided by sqrt(p), as printed in the lemma and Eq.(95). Eq.(96)'s operator
normalization by p is a uniquely determined typo and is not copied. -/
theorem normalizedKrausBranches {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (A : Superop J I) (hA : IsChannel A) (E : Superop I J) (hE : FiniteCPMap E)
    (hnorm : (E rho).trace = 1) :
    ∃ a e : ℕ, ∃ AK : Fin (a + 1) → Matrix I J ℂ,
      ∃ EK : Fin (e + 1) → Matrix J I ℂ,
        Represents AK A ∧ Represents EK E ∧
        0 < (conjSuperop (EK 0) rho).trace.re ∧
        fe rho (A ∘ E) ≤ operatorFe rho
          (AK 0 * ((((Real.sqrt ((conjSuperop (EK 0) rho).trace.re))⁻¹ : ℝ) : ℂ) • EK 0)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
