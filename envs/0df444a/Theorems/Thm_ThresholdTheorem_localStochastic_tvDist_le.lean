-- Prove2me | Theorems.Thm_ThresholdTheorem_localStochastic_tvDist_le
-- name    : ThresholdTheorem.localStochastic_tvDist_le
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T20:32:43.098256+00:00
-- url     : https://prove2.me/theorems/9ea2a98a-0c5f-484e-9352-b02be6b1ba0f
-- title:
--   Union bound: local stochastic noise of rate $e$ perturbs the output by at most $e\,|C|$ in total variation
-- statement:
--   Let $C$ be a layered circuit on a finite set of qubits $Q$ with $|C|$ locations, and let $e\ge 0$. If $P$ is the measured output distribution of $C$ under some local stochastic noise process of rate $e$ (`IsLocalStochasticDist C e P`), then
--   $$d_{\mathrm{TV}}\big(P,\;P_{\mathrm{ideal}}(C)\big)\;\le\;e\,|C|.$$
--   Proof idea: on runs whose fault set misses every location of $C$, the data evolve ideally and the environment is untouched, so the output is exactly ideal. The remaining runs have total weight at most $\sum_{\ell}\Pr[\ell\in F]\le e\,|C|$, and each of them contributes total variation at most $1$. This is the final union bound in the threshold theorem. It generalises the proved lemma `noisy_tv_le_fault_rate_mul_size` from independent to local stochastic noise.
-- source:
--   D. Gottesman, arXiv:0904.2557, Sec. 5, proof of Theorem 10 (final union bound over locations); generalises Prove2Me ThresholdTheorem.noisy_tv_le_fault_rate_mul_size to the local stochastic model of Definitions.Def_threshold_theorem_local_stochastic.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open ThresholdTheorem

namespace ThresholdTheorem
theorem localStochastic_tvDist_le {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (e : ℝ) (he : 0 ≤ e) (P : (Q → Fin 2) → ℝ) (hP : IsLocalStochasticDist C e P) :
    tvDist P (outDist (idealState C)) ≤ e * C.size := by sorry
end ThresholdTheorem
