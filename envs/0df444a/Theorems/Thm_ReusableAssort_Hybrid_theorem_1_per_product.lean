-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_theorem_1_per_product
-- name    : ReusableAssort.Hybrid.theorem_1_per_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:28.967998+00:00
-- url     : https://prove2.me/theorems/9fdda950-c617-48d4-b899-48a26e8d1e52
-- title:
--   Proof of Theorem 1, ec12 — per-product, per-time revenue of random discarding
-- statement:
--   Under the hypotheses of (EC.2) — model assumptions, $y$ feasible and normalized, product $i$ discarded at random with probability $\gamma \in [0,1]$, the other products under arbitrary valid rules, start at time $1$ with full inventory — the expected revenue collected from product $i$ at every time $t \in [T]$ satisfies
--   $$\mathbb E\big[r^{z_t}_i I_{i,t}\big] \ge (1-\gamma)\Big(1 - \exp\Big(-\frac{\gamma^2 c_i}{2-\gamma}\Big)\Big) \sum_{z} \sum_{S \in \mathcal S} F_t(z)\, r^{z}_i\, \phi^{z}(S, i)\, y_{S,t,z},$$
--   where $I_{i,t}$ indicates that a unit of product $i$ is rented at time $t$.
--
--   Summed over $t$ and $i$, this gives the competitive ratio $(1-\gamma)(1 - \exp(-\gamma^2 c_{\min}/(2-\gamma)))$ of Algorithm 2 against the LP.
--
--   **Formalization Note** As for (EC.2): $c_i$ in place of the page's $c_{\min}$ (stronger), arbitrary valid rules for the other products, and any feasible normalized $y$.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec12 (PDF 38), proof of Theorem 1 (display following "Now, fix any time t and product i")

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Process

namespace ReusableAssort.Hybrid

theorem theorem_1_per_product {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (rule : Fin n → Rule Z) (hrule : ∀ j, (rule j).Valid)
    (i : Fin n) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hi : rule i = Rule.random γ) :
    ∀ t ∈ Finset.Icc 1 T,
      (1 - γ) * (1 - Real.exp (-(γ ^ 2 * (I.c i : ℝ) / (2 - γ))))
          * ∑ z, ∑ S ∈ I.feas, I.F t z * I.r z i * I.phi z S i * y t z S
        ≤ expRevAt I y rule 1 (fun _ _ => 0) i t := by sorry

end ReusableAssort.Hybrid
