-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_eq_45
-- name    : QRepeaterBench.Dephasing.eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:46.757287+00:00
-- url     : https://prove2.me/theorems/e3014957-684a-4298-942e-c62d12033753
-- title:
--   Eq. (45) — for a unital, trace-preserving qudit map E, I_C(E) = I_RC(E) = log₂ d − S(ρ_E)
-- statement:
--   Let $d\ge1$ and let $\mathcal E$ be a linear map on $d\times d$ complex matrices which is **unital**, $\mathcal E(I)=I$, and **trace preserving**, $\mathrm{Tr}\,\mathcal E(X)=\mathrm{Tr}\,X$ for all $X$. Then the coherent information and the reverse coherent information of $\mathcal E$ coincide and
--
--   $$I_{(R)C}(\mathcal E)=\log_2 d-S(\rho_{\mathcal E}).$$
--
--   Both reduced states of the Choi matrix are maximally mixed, $I/d$: the reference one because the map preserves the trace, the output one because the map is unital.
--
--   **Formalization Note** The paper says "unital channels". The statement assumes only linearity, unitality and trace preservation; complete positivity is not used, so the statement covers every unital channel.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 8, Eq. (45)

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem eq_45 (d : ℕ) [NeZero d] (E : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) (hunital : E 1 = 1) (htp : ∀ X, (E X).trace = X.trace) : coherentInfo d ⇑E = reverseCoherentInfo d ⇑E ∧ coherentInfo d ⇑E = Real.logb 2 (d : ℝ) - QAlgorithms.vnEntropy (choi d ⇑E) := by sorry
end QRepeaterBench.Dephasing
