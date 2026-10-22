-- Prove2me | Theorems.Thm_WFMFG_Conv_lemma_4_9
-- name    : WFMFG.Conv.lemma_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:35.701681+00:00
-- url     : https://prove2.me/theorems/aa5234af-b34d-4201-9589-b4870a7c0c2b
-- title:
--   Lemma 4.9, p. 25 — discrete gradients of $z^{N,l}$ versus intrinsic gradients of $U$, remainder $C(y^m)^{1+\gamma'/2}/N^{1+\gamma'/2}$
-- statement:
--   Let $d \ge 1$, $\gamma' \in (0,1)$, $T > 0$ and let $U$ belong to the regularity class. There is $C$ such that for all $N \ge 1$, $l, m \in [\![N]\!]$, $t \in [0,T]$, $(x, y) \in [\![d]\!]^N \times \mathbb Y$ with $\mu = \mu^N_{x,y}$ in the interior of the simplex, and $j \in [\![d]\!]$, writing $z^{N,l}(t,x,y) = U^{x^l}(t,\mu^N_{x,y})$ and $\Delta^m z^{N,l}[j] = z^{N,l}(t,(j,x^{-m}),y) - z^{N,l}(t,x,y)$:
--
--   1. **(4.27)** for $m \ne l$:
--   $$
--   \Delta^m z^{N,l}(t,x,y)[j] = \frac{y^m}{N}\big(\mathfrak d_jU^{x^l}(t,\mu) - \mathfrak d_{x^m}U^{x^l}(t,\mu)\big) + \varrho^{N,l,m}(t,x,y)[j];
--   $$
--   2. **(4.28)**:
--   $$
--   \Delta^l z^{N,l}(t,x,y)[j] = U^j(t,\mu) - U^{x^l}(t,\mu) + \frac{y^l}{N}\big(\mathfrak d_jU^{j}(t,\mu) - \mathfrak d_{x^l}U^{j}(t,\mu)\big) + \varrho^{N,l,l}(t,x,y)[j];
--   $$
--
--   and in both cases (4.29) $|\varrho^{N,l,m}(t,x,y)[j]| \le C (y^m)^{1+\gamma'/2}/N^{1+\gamma'/2}$.
--
--   This lemma converts first-order variations in the $N$-player system into intrinsic derivatives on the simplex.
--
--   **Formalization Note.** The paper writes the left sides as $\frac1{y^l}\Delta^m u^{N,l}$ with $u^{N,l} = y^l z^{N,l}$; this equals $\Delta^m z^{N,l}$ when $y^l > 0$, and the statement is made for $z^{N,l}$ (Remark 4.7), so no division by $y^l$ occurs. It is stated where $\mu^N_{x,y}$ lies in the interior of the simplex, the only case the proof of Theorem 2.4 uses; at boundary points the printed $\mathfrak dU$ would be a continuous extension. In (4.28) the first-order term is written with $\mathfrak dU^{j}$: moving player $l$ to $j$ changes the evaluated component to $U^j$, and with the printed $\mathfrak dU^{x^l}$ the remainder is of order $y^l/N$, not covered by (4.29).
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 25, Lemma 4.9, (4.27)–(4.29)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem lemma_4_9 (d : ℕ) [NeZero d] (γ' T : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hT : 0 < T)
    (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (hU : WFReg γ' T U) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ (l m : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → (∀ i, 0 < empMeas x y i) → ∀ j : Fin d,
      (m ≠ l →
        |zN U l t (Function.update x m j) y - zN U l t x y
            - ((y m : ℝ) / N)
              * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) (x m))| ≤
          C * (y m : ℝ) ^ (1 + γ' / 2) / (N : ℝ) ^ (1 + γ' / 2)) ∧
      |zN U l t (Function.update x l j) y - zN U l t x y
          - (U j t (empMeas x y) - U (x l) t (empMeas x y))
          - ((y l : ℝ) / N) * (sD (U j t) (empMeas x y) j - sD (U j t) (empMeas x y) (x l))| ≤
        C * (y l : ℝ) ^ (1 + γ' / 2) / (N : ℝ) ^ (1 + γ' / 2) := by sorry

end WFMFG.Conv
