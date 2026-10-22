-- Prove2me | Theorems.Thm_WFMFG_Conv_lemma_4_10
-- name    : WFMFG.Conv.lemma_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:22.271879+00:00
-- url     : https://prove2.me/theorems/44cfb9fa-3481-453d-87a0-56ec55d9383c
-- title:
--   Lemma 4.10, p. 26 — the drift terms of the Nash system along $z^{N,l}$ match those of the master equation up to $C/N^\eta$ on $\mathcal T_N$
-- statement:
--   Let $\gamma' \in (0,1)$ and $\epsilon \in (0,\frac14)$. There is $\eta > 0$, depending only on $\gamma'$ and $\epsilon$, such that: for every $d \ge 1$, $T > 0$, $\delta > 0$, cutoff $\varphi$ (2.2) with parameters $\kappa, \delta$, and $U$ in the regularity class, there is $C$ such that for all $N \ge 1$, $l$, $t \in [0,T]$ and $(x, y) \in \mathcal T_N$, with $\mu = \mu^N_{x,y}$ and $z^{N,m}(t,x,y) = U^{x^m}(t,\mu^N_{x,y})$,
--   $$
--   \begin{aligned}
--   &\sum_{m}\varphi(\mu[\bullet])\cdot\Delta^m z^{N,l}[\bullet] + \sum_{m\ne l} a^*(x^m, z^{N,m}_\bullet)\cdot\Delta^m z^{N,l}[\bullet] \\
--   &\quad= \sum_{k,j}\mu[k]\varphi(\mu[j])\big(\mathfrak d_jU^{x^l} - \mathfrak d_kU^{x^l}\big)(t,\mu) + \sum_{k,j}\mu[k]\big(U^k - U^j\big)_+(t,\mu)\big(\mathfrak d_jU^{x^l} - \mathfrak d_kU^{x^l}\big)(t,\mu) + \sum_j\varphi(\mu[j])\big(U^j - U^{x^l}\big)(t,\mu) + r_2^{N,l}(t,x,y),
--   \end{aligned}
--   $$
--   with $|r_2^{N,l}(t,x,y)| \le C/N^\eta$.
--
--   Together with Lemmas 4.8 and 4.11 this identifies each term of the Nash system evaluated along $z^{N,l}$ with a term of the master equation.
--
--   **Formalization Note.** Stated for $z^{N,l}$ (Remark 4.7): the paper's $\frac1{y^l}\Delta^m u^{N,l}$ and $a^*(x^m, \frac1{y^m}u^{N,m}_\bullet)$ equal $\Delta^m z^{N,l}$ and $a^*(x^m, z^{N,m}_\bullet)$ when the weights are positive, and the $z$-form needs no division. $C$ is chosen after $\varphi$ as well as $U$: the drift is proportional to $\kappa$, so the constant cannot depend on $U$ alone as printed. The paper's "$\gamma$" in the dependence of $\eta$ is read as $\gamma'$. The master equation is not used.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 26, Lemma 4.10, (4.30)–(4.31)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem lemma_4_10 (γ' ϵ : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1 / 4) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (d : ℕ) [NeZero d] (T κ δ : ℝ), 0 < T → 0 < δ →
    ∀ φ : ℝ → ℝ, IsCutoff κ δ φ →
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y →
      |driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
          - (∑ k, ∑ j, empMeas x y k * φ (empMeas x y j)
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
            + ∑ k, ∑ j, empMeas x y k * pos (U k t (empMeas x y) - U j t (empMeas x y))
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
            + ∑ j, φ (empMeas x y j) * (U j t (empMeas x y) - U (x l) t (empMeas x y)))| ≤
        C / (N : ℝ) ^ η := by sorry

end WFMFG.Conv
