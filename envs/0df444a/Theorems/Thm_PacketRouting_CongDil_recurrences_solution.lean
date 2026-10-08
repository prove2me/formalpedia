-- Prove2me | Theorems.Thm_PacketRouting_CongDil_recurrences_solution
-- name    : PacketRouting.CongDil.recurrences_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:03:24.26228+00:00
-- url     : https://prove2.me/theorems/22727793-2a09-4e5f-bcda-75801e9e897e
-- title:
--   §3.2, pp. 12–13 — the recurrences for r^(i), I^(i) have solutions I^(j) = O(1), r^(j) = O(1) with j = O(log* d)
-- statement:
--   Let $\log=\log_2$, fix a constant $\kappa>0$ (the $O(1)$ of the recurrence) and a number $d$. Define the frame sizes and relative congestions of p. 13 by
--   $$
--   I^{(1)}=\log d,\quad I^{(i+1)}=\log^5 I^{(i)},\qquad r^{(1)}=1,\quad r^{(i+1)}=r^{(i)}\Bigl(1+\frac{\kappa}{\sqrt{\log I^{(i)}}}\Bigr)\quad(i\ge1).
--   $$
--   The recursion of the proof of Theorem 3.4 runs while $I^{(i)}$ is above a constant threshold $I_0$ and stops at the first index $j$ with $I^{(j)}<I_0$ ("The recursion terminates when the first of these inequalities fails to hold", p. 13).
--
--   **Claim (p. 13).** For every $\kappa>0$ there is $I_1$ such that for every threshold $I_0\ge I_1$ there is a constant $C$ with the following property: for every $d$ there is an index $j\ge1$ with
--   $$
--   I^{(j)}<I_0,\qquad I^{(i)}\ge I_0\ (1\le i<j),\qquad r^{(j)}\le C,\qquad j\le C\,(\log^* d+1).
--   $$
--
--   That is, the recurrences have solutions $I^{(j)}=O(1)$ and $r^{(j)}=O(1)$ for some $j=O(\log^* d)$, uniformly in $d$. This is the bookkeeping that keeps the relative congestion bounded through $O(\log^* d)$ refinements.
--
--   **Formalization Note** The threshold is universally quantified above $I_1$ because the proof's lemmas each need "$I$ sufficiently large", so the stopping threshold is dictated by them, not chosen freely. The $+1$ in $\log^* d+1$ covers the values of $d$ with $\log^* d=0$, where the recursion stops at $j=1$.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), pp. 12–13, proof of Theorem 3.4, the recurrences and their solution (unnumbered)

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Recurrences

namespace PacketRouting.CongDil

/-- The recurrences of Leighton–Maggs–Rao, p. 13, have solutions `I^{(j)} = O(1)` and
`r^{(j)} = O(1)` for some `j = O(log* d)`: for every constant `κ > 0` (the `O(1)` in
`r^{(i+1)} = r^{(i)}(1 + O(1)/√(log I^{(i)}))`) there is a threshold `I₁` such that for every
termination threshold `I₀ ≥ I₁` there is a constant `C` with the following property. For every
`d`, the recursion run until the first index `j ≥ 1` with `I^{(j)} < I₀` stops at a `j` with
`r^{(j)} ≤ C` and `j ≤ C (log* d + 1)`. -/
theorem recurrences_solution :
    ∀ κ : ℝ, 0 < κ → ∃ I₁ : ℝ, ∀ I₀ : ℝ, I₁ ≤ I₀ → ∃ C : ℝ, ∀ d : ℕ,
      ∃ j : ℕ, 1 ≤ j ∧ frameSizeSeq d j < I₀ ∧
        (∀ i : ℕ, 1 ≤ i → i < j → I₀ ≤ frameSizeSeq d i) ∧
        relCongSeq κ d j ≤ C ∧ (j : ℝ) ≤ C * ((logStar d : ℝ) + 1) := by sorry

end PacketRouting.CongDil
