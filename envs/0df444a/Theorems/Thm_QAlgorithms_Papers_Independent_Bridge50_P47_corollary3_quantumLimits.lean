-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_corollary3_quantumLimits
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.corollary3_quantumLimits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:46:07.434655+00:00
-- url     : https://prove2.me/theorems/7d3401d2-892b-4135-8427-fcc8d154c024
-- title:
--   Corollary 3: fixed-error quantum capacity limits
-- statement:
--   Let $\mathcal N$ be degradable on nonzero finite quantum systems, and let $0<\varepsilon<1/\sqrt2$. Define $N(n,\varepsilon)$ by unassisted transmission with worst purified error and $N_E(n,\varepsilon)$ by unassisted entanglement generation with a normalized joint input. Define $Q(\mathcal N)$ operationally by the infimum over positive errors of the liminf transmission rates. Then both limits exist and
--
--   $$
--   \lim_{n\to\infty}\frac{\log_2 N(n,\varepsilon)}n=Q(\mathcal N)=\lim_{n\to\infty}\frac{\log_2 N_E(n,\varepsilon)}n.
--   $$
--
--   Thus any one fixed error in this open interval recovers the vanishing-error quantum capacity. No achievability assertion is assumed as a hypothesis.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 5, Corollary 3: fixed-error quantum capacity limits

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Corollary 3, PDF p.5: both actual fixed-error limits, epsilon strictly positive.
The imported operational capacity uses vanishing entanglement-transmission error;
Section II, p.2 explicitly identifies these asymptotic capacity conventions. -/
theorem corollary3_quantumLimits [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : P67.IsDegradable U)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1 / Real.sqrt 2) :
    Tendsto (fun n : ℕ => logN U n epsilon / (n : ℝ)) atTop (nhds (P80.quantumCapacity (P67.receiverChannel U))) ∧
    Tendsto (fun n : ℕ => logNE U n epsilon / (n : ℝ)) atTop (nhds (P80.quantumCapacity (P67.receiverChannel U))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
