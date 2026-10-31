-- Prove2me | Theorems.Thm_SVFAppt_eq_3_waiting_max
-- name    : SVFAppt.eq_3_waiting_max
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:58.88445+00:00
-- url     : https://prove2.me/theorems/f39508ad-e895-4c06-a3b3-cbe7f964eb6d
-- title:
--   Eq. (3) — the waiting time is the maximum of a backward random walk
-- statement:
--   Fix a sequence $\tau$, a schedule $x$ and a realization $b$ of the service times, and let $W_k$ be the waiting times of the Lindley recursion (1). For every slot $k$ (with $k+1\le n$ in the paper's 1-based numbering), $W_{k+1}$ is the maximum of the random walk with steps $b_{\tau(k)}-x_{\tau(k)},\ b_{\tau(k-1)}-x_{\tau(k-1)},\dots,b_{\tau(1)}-x_{\tau(1)}$:
--
--   $$W_{k+1}=\max\Big\{0,\ \max\Big\{\sum_{i=j}^{k}\big(b_{\tau(i)}-x_{\tau(i)}\big):\ j\in\{1,\dots,k\}\Big\}\Big\}.$$
--
--   The statement asserts both forms: the explicit maximum of suffix sums, and the maximum $\max\{0,S_1,\dots,S_k\}$ of the walk whose $j$-th step is the step of slot $k-j+1$.
--
--   This turns the recursion into a functional of the steps that is convex in each step, which is the starting point of every bound in Section 3.
--
--   **Formalization Note** Lean slots are 0-based, so Lean's $W_k$ ($k<n$) is the paper's $W_{k+1}$; the index $j=k$ of the Lean maximum contributes the empty sum $0$. The statement is pathwise.
--
--   Differences from the source:
--   - encoding: slots and patients numbered 1, …, n → Fin n (0-based); Lean slot i is the paper's slot i + 1; reason: Lean convention; same instances
--   - reading: initial waiting and idle times not stated → W_0 = I_0 = 0 (the paper's W_1 = I_1 = 0); reason: the paper's identity (5) holds exactly under this convention; the first patient arrives to an idle doctor
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, §2.2, eq. (3), p. 9

import Mathlib
import Definitions.Def_SVFAppt_lindley
import Definitions.Def_SVFAppt_walkMax

namespace SVFAppt

/-- **Eq. (3): the waiting time is the maximum of a backward random walk.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, §2.2, eq. (3), p. 9: "It follows by iterating the
Lindley recursion (1) that Wk+1 is the maximum of a random walk with steps Bτ(k) − xτ(k),
Bτ(k−1) − xτ(k−1), . . . , Bτ(1) − xτ(1), that is,
Wk+1 = max{0, max{Σ_{i=j}^{k} Bτ(i) − xτ(i) : j ∈ {1, . . . , k}}}."

For every sequence `τ`, schedule `x`, realization `b` of the service times and 0-based slot
`k < n`:
1. `W_k = max{0, max_{0 ≤ j < k} Σ_{i=j}^{k−1} (b_{τ(i)} − x_{τ(i)})}` (eq. (3); the index
   `j = k` below contributes the empty sum `0`);
2. `W_k = walkMax` of the steps `b_{τ(k−1)} − x_{τ(k−1)}, …, b_{τ(0)} − x_{τ(0)}` (backward order,
   the form used in (4)).

**Formalization Note** Slots are 0-based: Lean `W_k` is the paper's `W_{k+1}`, and Lean slot `i`
is the paper's slot `i + 1`. The statement is pathwise (no probability). -/
theorem eq_3_waiting_max {n : ℕ} (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    wait τ x b k = (Finset.range (k + 1)).sup' ⟨k, by simp⟩
        (fun j => ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ i.val ∧ i.val < k),
          (b (τ i) - x (τ i))) ∧
      wait τ x b k = walkMax (fun j : Fin k =>
        b (τ ⟨k - 1 - j.val, by have := j.isLt; omega⟩) -
          x (τ ⟨k - 1 - j.val, by have := j.isLt; omega⟩)) := by sorry

end SVFAppt
