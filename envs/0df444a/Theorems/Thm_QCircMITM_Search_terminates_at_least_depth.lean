-- Prove2me | Theorems.Thm_QCircMITM_Search_terminates_at_least_depth
-- name    : QCircMITM.Search.terminates_at_least_depth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:08.912643+00:00
-- url     : https://prove2.me/theorems/241f2e36-9cef-4973-96fc-45c646d788b4
-- title:
--   §3, p. 6 — MITM-factor stops at the least positive depth (corrected: depths 1 … 2⌈l/2⌉; depth 0 is never tested)
-- statement:
--   Let $V \subseteq U(2^n)$ be a finite set of unitaries (standing for $\mathcal V_{n,\mathcal G}$), $U$ a unitary and $l \ge 0$. Write $h = \lceil l/2\rceil$.
--
--   1. If $d$ is the least positive depth at which $U$ can be implemented over $V$ (that is, $1 \le d$, $U \in S_d$ and $U \notin S_{d'}$ for $1 \le d' < d$), and $d \le 2h$, then MITM-factor$(\mathcal G, U, l)$ returns a circuit $c$ with every layer in $V$, implementing $U$, and of depth exactly
--   $$|c| = d .$$
--   2. If $U \notin S_d$ for every $1 \le d \le 2h$, then MITM-factor$(\mathcal G, U, l)$ returns nothing.
--
--   This is the paper's claim that the algorithm "terminates at the smallest depth for which there exists a circuit implementing $U$", stated in the form the pseudocode actually supports (see the note).
--
--   **Formalization Note.** Two corrections to the printed sentence, both forced by the pseudocode. (i) For odd $l$ the last iteration $i = h$ also tests depth $2h = l+1$, so the depths searched are $1,\dots,2\lceil l/2\rceil$ rather than $1,\dots,l$. (ii) The loop starts at $i = 1$, so depth $0$ is never tested: for $U = I$ the algorithm returns a circuit of the least *positive* depth, not the empty circuit. The statement holds for every finite set of unitaries $V$.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 6, §3 (paragraph after the MITM-factor pseudocode)

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

namespace QCircMITM.Search

theorem terminates_at_least_depth {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) :
    (∀ d : ℕ, 1 ≤ d → d ≤ 2 * ((l + 1) / 2) → U ∈ S V d →
        (∀ d' : ℕ, 1 ≤ d' → d' < d → U ∉ S V d') →
        ∃ c, mitmFactor V U l = some c ∧ c.length = d ∧ (∀ W ∈ c, W ∈ V) ∧ c.prod = U) ∧
    ((∀ d : ℕ, 1 ≤ d → d ≤ 2 * ((l + 1) / 2) → U ∉ S V d) → mitmFactor V U l = none) := by sorry

end QCircMITM.Search
