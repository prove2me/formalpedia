-- Prove2me | Theorems.Thm_QualityEncroach_Differ_lemma_1_i
-- name    : QualityEncroach.Differ.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:02.886734+00:00
-- url     : https://prove2.me/theorems/f88e97c7-effb-4be2-8462-1381058d6c3f
-- title:
--   Lemma 1(i), p. 29 — for t ≤ 1, the optimal ratio is t(u) = 6/5 − (2/5)√(4 − 5c/(ku²)) if c ≤ 3ku²/4, else 1
-- statement:
--   Fix $k>0$, $c\ge0$ and a direct quality $u>0$, and consider the manufacturer's reduced profit for high-quality encroachment ($0<t\le1$),
--
--   $$
--   \Pi_M(t,u)=\frac{4k^2u^3t^3-(8k^2u^3+8kcu)t^2-(k^2u^3+2kcu+\frac{c^2}{u})t+8k^2u^3+16kcu+\frac{8c^2}{u}}{4(8-5t)}-\frac{2ku^2-u+2c}{4}.
--   $$
--
--   1. If $c\le \tfrac{3ku^2}{4}$, then $t(u)=\tfrac65-\tfrac25\sqrt{4-\tfrac{5c}{ku^2}}$ lies in $(0,1]$ and is the unique maximizer of $t\mapsto\Pi_M(t,u)$ on $(0,1]$.
--   2. If $c>\tfrac{3ku^2}{4}$, then $t=1$ is the unique maximizer of $t\mapsto\Pi_M(t,u)$ on $(0,1]$.
--
--   The lemma determines how far the manufacturer differentiates the retailer's product below her own when she encroaches with the higher quality.
--
--   **Formalization Note.** The lemma is stated "suppose encroachment happens", and its proof maximizes under the constraint (11) ($q_M>0$) and $t\le1$, concluding $t(u)=\min\{t_1,1\}$ from the sign of $\partial\Pi_M/\partial t$ on $[0,1]$ alone. The formal statement is that conclusion: the maximizer over all of $(0,1]$.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 29, Lemma 1(i) and its proof

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Reduced

namespace QualityEncroach.Differ

theorem lemma_1_i (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (u : ℝ) (hu : 0 < u) :
    (c ≤ 3 * k * u ^ 2 / 4 →
      tH k c u ∈ Set.Ioc 0 1 ∧
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, t ≠ tH k c u → PiH k c t u < PiH k c (tH k c u) u) ∧
    (3 * k * u ^ 2 / 4 < c →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, t ≠ 1 → PiH k c t u < PiH k c 1 u) := by sorry

end QualityEncroach.Differ
