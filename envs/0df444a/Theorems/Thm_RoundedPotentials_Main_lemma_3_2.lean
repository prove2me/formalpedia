-- Prove2me | Theorems.Thm_RoundedPotentials_Main_lemma_3_2
-- name    : RoundedPotentials.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:34:09.268261+00:00
-- url     : https://prove2.me/theorems/9ed2ed87-bbcf-4d26-a34e-7fef8a3842d1
-- title:
--   Lemma 3.2 — single-pair correctness
-- statement:
--   Let the capacities be nonnegative integers bounded by $W\ge1$, with $n$ vertices, $s\ne t$, and an integer $p\ge0$. For any real potential vector $y$, if
--   $$y_v\in[0,n-1]\cup[n,2n-1],\quad y_s\ge n,\quad y_t\le n-1,\qquad
--   |\operatorname{ex}_{f^y}(v)-p(1[v=s]-1[v=t])|\le\frac1{8n}\quad(v\in V),$$
--   then $\operatorname{MaxFlow}(s,t)=p$.
--
--   This is soundness for real potentials, without any grid restriction. The induced assignment uses the clipped potential drop exactly as in eq. (1).
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and an edge list with distinct loopless ordered pairs; reason: relabeling preserves every flow and cut; m is the actual list length; zero capacities are explicitly allowed in §3
--   - encoding: MaxFlow(s,t) = p → IsGreatest of the set of real values of published IsFlow assignments; reason: records attainment without a real supremum default; the published definition has the same signed conservation equations
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 13, Lemma 3.2, eqs. (6), (7)

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Certificate

namespace RoundedPotentials.Main
open scoped BigOperators

theorem lemma_3_2 {n W : ℕ} (I : Instance n W) (hW : 1 ≤ W)
    (s t : Fin n) (hst : s ≠ t) (p : ℤ) (hp : 0 ≤ p) (y : Fin n → ℝ)
    (hchecks : CertificateChecks I n s t p y) :
    MaxValue I s t (p : ℝ) := by sorry

end RoundedPotentials.Main
