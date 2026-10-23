-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_eq_EC_2
-- name    : ReusableAssort.Hybrid.eq_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:26.845985+00:00
-- url     : https://prove2.me/theorems/a38d5924-f2ee-42e5-8e38-7f988085455d
-- title:
--   (EC.2), ec10 — a randomly discarded product has no unit on hand w.p. ≤ exp(−γ²c_i/(2−γ))
-- statement:
--   Consider an instance satisfying the model assumptions, a feasible and normalized solution $y$ of Expected-LP$[\{F_t\}]$, and run the online process from time $1$ with full inventory, where product $i$ is discarded at random with probability $\gamma \in [0,1]$ and every other product uses an arbitrary valid discarding rule. Then for every time $t \in [T]$,
--   $$\Pr\Big[\sum_{\tau < t} I_{i,\tau}\, I_{i,\tau,t} \ge c_i\Big] \le \exp\Big(-\frac{\gamma^2 c_i}{2-\gamma}\Big),$$
--   where $I_{i,\tau}$ indicates that a unit of $i$ is rented at time $\tau$ and $I_{i,\tau,t}$ that its rental duration exceeds $t - \tau$. The event on the left is exactly "no unit of product $i$ is on hand at the beginning of time $t$".
--
--   This tail bound is the core of the analysis of random discarding (Theorem 1): it shows that a randomly discarded product is available with probability at least $1 - \exp(-\gamma^2 c_i/(2-\gamma))$ at every time.
--
--   **Formalization Note** The page states the bound with $c_{\min}$; its proof gives it with $c_i \ge c_{\min}$, which is stronger and is what the hybrid algorithm needs. The rules of the other products are arbitrary (Theorem 3's proof relies on this), and $y$ need only be feasible, not optimal (the proof uses only the inventory constraints of product $i$). The event uses the convention $\bar G(k) = \Pr[d > k]$ of the LP: a unit rented at $\tau$ is still out at $t$ iff $d > t - \tau$.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec10 (PDF 36), eq. (EC.2) in the proof of Theorem 1

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Process

namespace ReusableAssort.Hybrid

theorem eq_EC_2 {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (rule : Fin n → Rule Z) (hrule : ∀ j, (rule j).Valid)
    (i : Fin n) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hi : rule i = Rule.random γ) :
    ∀ t ∈ Finset.Icc 1 T,
      probNoUnit I y rule 1 (fun _ _ => 0) i t
        ≤ Real.exp (-(γ ^ 2 * (I.c i : ℝ) / (2 - γ))) := by sorry

end ReusableAssort.Hybrid
