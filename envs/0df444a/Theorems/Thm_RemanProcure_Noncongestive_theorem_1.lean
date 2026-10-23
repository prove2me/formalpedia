-- Prove2me | Theorems.Thm_RemanProcure_Noncongestive_theorem_1
-- name    : RemanProcure.Noncongestive.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:17.661032+00:00
-- url     : https://prove2.me/theorems/000f4f6d-bcd8-42c9-8639-dcc8a834caac
-- title:
--   Theorem 1, pp. 1445–1446 — the optimal policy is state-dependent noncongestive acquisition: acquire iff x_i < S*_i(x_{−i}) for all i, with properties (i)–(iv)
-- statement:
--   Consider the core acquisition model under the standing assumptions of §2, with optimal cost function $v^*$, acquisition gap $\Delta(x)=c_A+\sum_i p_iv^*(x+e_i)-v^*(x)$ (acquiring is optimal in $x$ when $\Delta(x)\le0$), and acquire-up-to levels $S^*_i(x_{-i})\in\mathbb N_0\cup\{\infty\}$, the least value of $x_i$ at which acquiring stops being optimal when the other coordinates are $x_{-i}$. Then the optimal stationary policy is a state-dependent noncongestive-acquisition policy:
--   $$\text{it is optimal to acquire in } x\iff x_i<S^*_i(x_{-i})\ \text{ for all } i,$$
--   and moreover:
--   1. **(i)** $S^*_i$ weakly decreases as the number of cores of a type $j\ne i$ increases: $S^*_i\big((x+e_j)_{-i}\big)\le S^*_i(x_{-i})$;
--   2. **(ii)** $S^*_i$ weakly decreases as the quality of a core of a type $j\ne i$ increases: for types $q<w$, both different from $i$, $S^*_i\big((x+e_q)_{-i}\big)\le S^*_i\big((x+e_w)_{-i}\big)$;
--   3. **(iii)** it is always optimal to satisfy a demand if cores are available: if $x\ne0$ there is a type $i$ with $x_i>0$ and $v^*(x-e_i)+r_i\le v^*(x)+c_L$;
--   4. **(iv)** it is always optimal to remanufacture a core of the highest available quality: if $i$ is the best available type ($x_i>0$ and $x_j=0$ for all $j<i$), then $v^*(x-e_i)+r_i\le v^*(x-e_j)+r_j$ for every available type $j$.
--
--   This is the main structural result of the paper: acquisition is governed by a threshold for each core type that depends on the other inventories and their quality mix, and remanufacturing always fulfils demand with the best core.
--
--   **Formalization Note** $v^*$ is the value-iteration limit of equation (1); $S^*_i$ is the canonical level defined from $v^*$ (not an arbitrary threshold), with value $\infty$ when acquiring is optimal for every $x_i$. Ties count as acquiring. Point (ii) is read as moving one core from type $w$ to the better type $q<w$, with $q,w\ne i$. Types are indexed by `Fin K` with index $0$ the paper's type 1. The standing assumptions include the disclosed additions $K\ge1$, $p$ a probability vector, $r_i\ge0$, $c_A\ge0$, $\mu,\lambda>0$.
-- source:
--   Nadar, Akan, Debo & Scheller-Wolf, Optimal Procurement in Remanufacturing Systems with Uncertain Used-Item Condition, Oper. Res. 71(5) (2023), pp. 1445–1446 (PDF 6–7), Theorem 1

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model

namespace RemanProcure.Noncongestive
theorem theorem_1 {K : ℕ} (P : Params K) (hP : Standing P) : (∀ x : Fin K → ℕ, AcqOpt P x ↔ ∀ i, ((x i : ℕ) : ℕ∞) < Sstar P i x) ∧ (∀ (i j : Fin K), j ≠ i → ∀ x : Fin K → ℕ, Sstar P i (x + e j) ≤ Sstar P i x) ∧ (∀ (i q w : Fin K), q < w → q ≠ i → w ≠ i → ∀ x : Fin K → ℕ, Sstar P i (x + e q) ≤ Sstar P i (x + e w)) ∧ (∀ x : Fin K → ℕ, (∃ i, 0 < x i) → ∃ i, 0 < x i ∧ vstar P (x - e i) + P.r i ≤ vstar P x + P.cL) ∧ (∀ (x : Fin K → ℕ) (i : Fin K), 0 < x i → (∀ j, j < i → x j = 0) → ∀ j, 0 < x j → vstar P (x - e i) + P.r i ≤ vstar P (x - e j) + P.r j) := by sorry
end RemanProcure.Noncongestive
