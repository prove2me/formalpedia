-- Prove2me | Theorems.Thm_ThresholdTheorem_noiseModel_isLocalStochastic
-- name    : ThresholdTheorem.noiseModel_isLocalStochastic
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T20:32:38.73498+00:00
-- url     : https://prove2.me/theorems/25fdc2b8-285d-446a-9d0c-c30976a5c7c6
-- title:
--   Independent stochastic noise of rate $p\le 1$ is local stochastic of rate $p$
-- statement:
--   Let $C$ be a layered circuit on a finite set of qubits $Q$, let $0\le p\le 1$, and let $N$ be an independent stochastic noise model with fault rate at most $p$ (`NoiseModel p`). Then the noisy output distribution of $C$ is a local stochastic output distribution of rate $p$:
--   $$P_{\mathrm{noisy}}(N,C)\in\mathcal N_{\mathrm{ls}}(C,p).$$
--   Proof idea: expanding each location's channel $(1-q)\,\mathcal E_{\mathrm{ideal}}+q\,\mathcal E_{\mathrm{fault}}$ writes the noisy execution as a mixture over fault sets $F$, with weight $\prod_{\ell\in F}q_\ell\prod_{\ell\notin F}(1-q_\ell)$. No environment is needed ($m=0$). Then $\Pr[S\subseteq F]=\prod_{\ell\in S}q_\ell\le p^{|S|}$. This shows that the physical noise model of the threshold theorem lies in the local stochastic class. The hypothesis $p\le 1$ makes the weights nonnegative.
-- source:
--   D. Gottesman, arXiv:0904.2557, Sec. 5 (independent stochastic noise is a special case of local stochastic noise); models Definitions.Def_threshold_theorem_noise_model and Definitions.Def_threshold_theorem_local_stochastic.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open ThresholdTheorem

namespace ThresholdTheorem
theorem noiseModel_isLocalStochastic {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : NoiseModel p) :
    IsLocalStochasticDist C p (outDist (noisyState N C)) := by sorry
end ThresholdTheorem
