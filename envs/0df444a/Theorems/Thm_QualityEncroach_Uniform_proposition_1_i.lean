-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_proposition_1_i
-- name    : QualityEncroach.Uniform.proposition_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:05.293588+00:00
-- url     : https://prove2.me/theorems/cdf61e19-a33e-4d53-ac45-8e4c6ee1863e
-- title:
--   Proposition 1(i), p. 11 — a threshold c̃ > 0 such that the manufacturer encroaches iff c < c̃
-- statement:
--   Let $k>0$. There is a threshold $\tilde c>0$, depending only on $k$, such that for every direct selling cost $c\ge 0$ and every subgame perfect equilibrium of the encroachment game with uniform quality,
--
--   1. if $c<\tilde c$, the manufacturer encroaches: $q^U_M>0$ on the equilibrium path;
--   2. if $c>\tilde c$, she does not: $q^U_M=0$ on the equilibrium path.
--
--   This is the first part of Proposition 1 (the proof finds $\tilde c\approx 0.1019/k$).
--
--   **Formalization Note.** The boundary point $c=\tilde c$ is left open: there the manufacturer is indifferent, and the paper writes "$c<\tilde c$" in Proposition 1 but "$c\le c_2$" with $c_2=\tilde c$ in Table 1 and Claim 2. The threshold is quantified before $c$, so it does not depend on $c$.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 11, Proposition 1(i); proof pp. 26–28

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- Proposition 1(i), p. 11: for every quality cost `k > 0` there is a threshold `c̃ > 0` such
that, in every subgame perfect equilibrium, the manufacturer encroaches if `c < c̃` and does not
if `c > c̃`. -/
theorem proposition_1_i (k : ℝ) (hk : 0 < k) : ∃ ct : ℝ, IsEncroachThreshold k ct := by sorry

end QualityEncroach.Uniform
