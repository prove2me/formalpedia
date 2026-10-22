-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_eq_95_flux_meets_coherent_information
-- name    : QRepeaterBench.Dephasing.eq_95_flux_meets_coherent_information
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:34.789658+00:00
-- url     : https://prove2.me/theorems/37d1aef2-9824-4826-a6ef-da5fb9f2675c
-- title:
--   Eqs. (94)–(95) — for the qudit dephasing channel, I_C = I_RC = log₂ d − H(P) and the entanglement flux Φ(P_d) ≤ log₂ d − H(P)
-- statement:
--   Let $d\ge2$ and $p\in[0,1]$, and let $\mathcal P_d$ be the qudit dephasing channel with binomial weights $\mathbf P=\{P_m(p,d)\}_{m=0}^{d-1}$. Then:
--
--   1. the coherent information of the channel is $I_C(\mathcal P_d)=\log_2 d-H(\mathbf P)$;
--   2. the reverse coherent information equals it, $I_{RC}(\mathcal P_d)=I_C(\mathcal P_d)$;
--   3. the entanglement flux satisfies
--
--   $$\Phi(\mathcal P_d)=E_R(\rho_{\mathcal P_d})\le\log_2 d-H(\mathbf P).$$
--
--   The lower bound $I_C$ and the upper bound $\Phi$ on the two-way assisted quantum and secret-key capacities therefore meet at $\log_2 d-H(\mathbf P)$, which is how the paper determines $Q_2(\mathcal P_d)=K(\mathcal P_d)=\log_2 d-H(\mathbf P)$.
--
--   **Formalization Note** The capacities $Q_2$ and $K$ themselves are not formalized: the statement is the coincidence of the two bounds. $\Phi$ takes values in $[0,\infty]$ and the bound is embedded with `ENNReal.ofReal`; since $H(\mathbf P)\le\log_2 d$, nothing is lost.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 11, Eqs. (94)–(95); announced as Eq. (20), p. 5

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem eq_95_flux_meets_coherent_information (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : coherentInfo d (dephasing d p) = Real.logb 2 (d : ℝ) - shannonEntropy (weight d p) ∧ reverseCoherentInfo d (dephasing d p) = coherentInfo d (dephasing d p) ∧ flux d (dephasing d p) ≤ ENNReal.ofReal (Real.logb 2 (d : ℝ) - shannonEntropy (weight d p)) := by sorry
end QRepeaterBench.Dephasing
