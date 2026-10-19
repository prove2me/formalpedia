-- Prove2me | Theorems.Thm_WFMFG_Conv_lemma_4_11
-- name    : WFMFG.Conv.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:24.00189+00:00
-- url     : https://prove2.me/theorems/4ef7d1f1-6a49-4089-ac7c-2593c8ced21c
-- title:
--   Lemma 4.11, p. 26 — the Hamiltonian along $z^{N,l}$ is $H(x^l, U(t,\mu^N_{x,y}))$ up to $C y^l/N$
-- statement:
--   Let $d \ge 1$, $\gamma' \in (0,1)$, $T > 0$ and let $U$ belong to the regularity class. There is a constant $C$ such that for every $\epsilon \in (0,\frac14)$, $N \ge 1$, $t \in [0,T]$, $(x,y) \in \mathcal T_N$ and $l \in [\![N]\!]$,
--   $$
--   H\big(x^l, z^{N,l}_\bullet(t,x,y)\big) = H\big(x^l, U(t,\mu^N_{x,y})\big) + r_3^{N,l}(t,x,y), \qquad |r_3^{N,l}(t,x,y)| \le C\,\frac{y^l}{N},
--   $$
--   where $z^{N,l}_\bullet(t,x,y) = \big(U^j(t, \mu^N_{(j,x^{-l}),y})\big)_{j}$, $U(t,\mu) = (U^j(t,\mu))_j$ and $H(i,u) = -\frac12\sum_{j\ne i}(u^i - u^j)_+^2$.
--
--   This is the Hamiltonian part of the identification of the Nash system along $z^{N,l}$ with the master equation.
--
--   **Formalization Note.** The paper's $H(x^l, \frac1{y^l}u^{N,l}_\bullet)$ is $H(x^l, z^{N,l}_\bullet)$ when $y^l > 0$; the statement is made for $z^{N,l}$ (Remark 4.7). $C$ depends only on $d$ and $U$ (through the regularity class), and is chosen before $\epsilon$ and the point.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 26, Lemma 4.11, (4.32)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem lemma_4_11 (d : ℕ) [NeZero d] (γ' T : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hT : 0 < T)
    (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (hU : WFReg γ' T U) :
    ∃ C : ℝ, ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 / 4 → ∀ N : ℕ, 1 ≤ N →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y →
      |ham (x l) (fun j => zN U l t (Function.update x l j) y)
          - ham (x l) (fun j => U j t (empMeas x y))| ≤
        C * (y l : ℝ) / N := by sorry

end WFMFG.Conv
