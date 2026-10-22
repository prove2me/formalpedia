-- Prove2me | Theorems.Thm_WFMFG_Conv_lemma_4_8
-- name    : WFMFG.Conv.lemma_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:23.395991+00:00
-- url     : https://prove2.me/theorems/27f45141-e55a-4145-85d4-9e31d0cf1f19
-- title:
--   Lemma 4.8, p. 25 — the common-noise term applied to $u^{N,l}$ is the Wright–Fisher operator of $U$ up to $C/N^\eta$ on $\mathcal T_N$
-- statement:
--   Let $\gamma' \in (0,1)$ and $\epsilon \in (0, \frac14)$. There is an exponent $\eta > 0$, depending only on $\gamma'$ and $\epsilon$, with the following property. Let $d \ge 1$, $T > 0$, and let $U = (U^1,\dots,U^d)$ belong to the regularity class (continuous on $[0,T]\times\mathcal S_{d-1}$, differentiable along the simplex in the interior, $U$ and $\mathfrak dU$ bounded, $\mathfrak dU$ and $\sqrt{p_jp_k}\,\mathfrak d^2_{j,k}U$ bounded and $\gamma'/2$-Hölder). Then there is $C$ such that for all $N \ge 1$, $l \in [\![N]\!]$, $t \in [0,T]$ and $(x,y) \in \mathcal T_N$ with $y^l > 0$, writing $\mu = \mu^N_{x,y}$ and $u^{N,l} = y^l U^{x^l}(t,\mu^N_{x,y})$,
--   $$
--   \frac{1}{y^l} N\,\mathbf E\big[u^{N,l}(t, x, y') - u^{N,l}(t,x,y)\big] = \sum_j(\delta_{j,x^l} - \mu[j])\,\mathfrak d_j U^{x^l}(t,\mu) + \frac12\sum_{j,k}(\mu[j]\delta_{j,k} - \mu[j]\mu[k])\,\mathfrak d^2_{j,k}U^{x^l}(t,\mu) + r_1^{N,l}(t,x,y),
--   $$
--   with $|r_1^{N,l}(t,x,y)| \le C/N^\eta$. Here $y' = \big(y^m S[x^m]/(N\mu[x^m])\big)_m$ with $S \sim \mathcal M_{N,\mu}$.
--
--   This identifies the common noise of the $N$-player game with the second-order Wright–Fisher (Kimura) part of the master equation; note that the right side carries no factor $\varepsilon$.
--
--   **Formalization Note.** The printed $u^{N,l}(x, \dots)$ on the left lacks its time argument; it is $t$. The hypothesis $y^l > 0$ is implicit in $1/y^l$. The lemma uses only the regularity of $U$, not the master equation, so it is stated for every $U$ in the regularity class, which replaces the Wright–Fisher Hölder space. $C$ is chosen after $U$, $d$, $T$ (and $\gamma'$, $\epsilon$), before $N$ and the point.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 25, Lemma 4.8, (4.25)–(4.26)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem lemma_4_8 (γ' ϵ : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1 / 4) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (d : ℕ) [NeZero d] (T : ℝ), 0 < T →
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y → 0 < y l →
      |(1 / (y l : ℝ)) * N
            * multE N (empMeas x y) (fun k => uN U l t x (reweight x y k) - uN U l t x y)
          - ∑ j, ((if j = x l then 1 else 0) - empMeas x y j) * sD (U (x l) t) (empMeas x y) j
          - (1 / 2) * ∑ j, ∑ k,
              (empMeas x y j * (if j = k then 1 else 0) - empMeas x y j * empMeas x y k)
                * sD2 (U (x l) t) (empMeas x y) j k| ≤
        C / (N : ℝ) ^ η := by sorry

end WFMFG.Conv
