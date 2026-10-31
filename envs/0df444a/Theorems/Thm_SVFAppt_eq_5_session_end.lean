-- Prove2me | Theorems.Thm_SVFAppt_eq_5_session_end
-- name    : SVFAppt.eq_5_session_end
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:57.993242+00:00
-- url     : https://prove2.me/theorems/5a9c8254-2c83-4540-ad5a-ad2db591bcab
-- title:
--   Eq. (5) — the session-end identity
-- statement:
--   Fix $n\ge1$, a sequence $\tau$, a schedule $x$ and a realization $b$ of the service times. The Lindley recursion (1) implies $W_{i+1}-I_{i+1}=W_i+b_{\tau(i)}-x_{\tau(i)}$, and summing over $i$ gives
--
--   $$\sum_{i=1}^n I_i+\sum_{i=1}^n b_i=\sum_{i=1}^{n-1}x_{\tau(i)}+W_n+b_{\tau(n)}.$$
--
--   Both sides are the time at which the last patient has been served (the "session end time"). Taking expectations under the mean-based schedule $x=\mu$ gives $\sum_i\mathbb EI_i=\mathbb EW_n$, which reduces the cost to waiting times only.
--
--   **Formalization Note** 0-based: Lean's $W_{n-1}$ and slot $n-1$ are the paper's $W_n$ and slot $n$; the sum $\sum_{i=1}^{n-1}$ runs over Lean slots $i$ with $i+1<n$. The identity is pathwise.
--
--   Differences from the source:
--   - encoding: slots and patients numbered 1, …, n → Fin n (0-based); Lean slot i is the paper's slot i + 1; reason: Lean convention; same instances
--   - reading: initial waiting and idle times not stated → W_0 = I_0 = 0 (the paper's W_1 = I_1 = 0); reason: the paper's identity (5) holds exactly under this convention; the first patient arrives to an idle doctor
--   - encoding: n patients (n ≥ 1 implicit: the identity names B_τ(n)) → hypothesis 0 < n; reason: for n = 0 the right-hand side refers to a nonexistent slot; excludes only an undefined case
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, §2.2, eq. (5), p. 10

import Mathlib
import Definitions.Def_SVFAppt_lindley

namespace SVFAppt

/-- **Eq. (5): the session-end identity.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, §2.2, eq. (5), p. 10: "Note that (1) implies
Wi+1 − Ii+1 = Wi + Bτ(i) − xτ(i). Summing over i we find the identity
Σ_{i=1}^{n} Ii + Σ_{i=1}^{n} Bi = Σ_{i=1}^{n−1} xτ(i) + Wn + Bτ(n)".

For `n ≥ 1`, every sequence `τ`, schedule `x` and realization `b` of the service times,
`Σ_{i<n} I_i + Σ_j b_j = Σ_{i<n−1} x_{τ(i)} + W_{n−1} + b_{τ(n−1)}`.

**Formalization Note** Slots are 0-based: Lean `W_{n−1}` and slot `n−1` are the paper's `W_n` and
slot `n`. The identity is pathwise; `W_0 = I_0 = 0` (the paper's `W_1 = I_1 = 0`) is built into
`lindley`. `n − 1` is natural-number subtraction under `0 < n`. -/
theorem eq_5_session_end {n : ℕ} (hn : 0 < n) (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) :
    ∑ i : Fin n, idle τ x b i + ∑ j : Fin n, b j =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n), x (τ i)
        + wait τ x b (n - 1) + b (τ ⟨n - 1, by omega⟩) := by sorry

end SVFAppt
