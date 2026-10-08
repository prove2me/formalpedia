-- Prove2me | Theorems.Thm_QualityEncroach_Differ_lemma_1_ii
-- name    : QualityEncroach.Differ.lemma_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:22.884146+00:00
-- url     : https://prove2.me/theorems/9686694e-5f59-45e5-9123-071599e7505e
-- title:
--   Lemma 1(ii), pp. 29, 33 — for t ≥ 1, the optimal ratio of (14) on [1, t̄_r): (2 + 5ku + √(…))/(12ku), or 1
-- statement:
--   Fix $k>0$, $c\ge0$ and $u>0$, and consider the manufacturer's reduced profit (14) for low-quality encroachment ($t\ge1$, the retailer carries the higher quality $tu$):
--
--   $$
--   \Pi_M(t,u)=\frac{4k^2u^3t^4-8ku^2t^3+4u(-2kc-2k^2u^2+2ku+1)t^2}{4(8t-5)}+\frac{8\bigl(c^2+cu(2ku-1)+ku^3(ku-1)\bigr)t}{4u(8t-5)}-\frac{(c+u(ku-1))^2}{4u(8t-5)},
--   $$
--
--   over the ratios $t\in[1,\bar t_r)$ at which the retailer's quantity is positive, where $\bar t_r=\frac{1+\sqrt{4kc+4k^2u^2-4ku+1}}{2ku}$. Assume $\bar t_r>1$, and let
--
--   $$
--   t^L(u)=\frac{2+5ku+\sqrt{4-48kc+8ku-23k^2u^2}}{12ku}.
--   $$
--
--   1. If $c\le\frac{3u-6ku^2}{4}$, then $t^L(u)\in[1,\bar t_r)$ is the unique maximizer of $\Pi_M(\cdot,u)$ on $[1,\bar t_r)$.
--   2. If $\frac{3u-6ku^2}{4}<c<\frac{4+8ku-23k^2u^2}{48k}$ and $u\le\frac{2}{7k}$, then $t^L(u)\in[1,\bar t_r)$, the maximum of $\Pi_M(\cdot,u)$ on $[1,\bar t_r)$ is $\max\{\Pi_M(1,u),\Pi_M(t^L(u),u)\}$, and every maximizer is $1$ or $t^L(u)$.
--   3. Otherwise, i.e. if $c>\frac{3u-6ku^2}{4}$ and either $c\ge\frac{4+8ku-23k^2u^2}{48k}$ or $u>\frac{2}{7k}$, then $t=1$ is the unique maximizer on $[1,\bar t_r)$.
--
--   Together with Lemma 1(i) this describes the manufacturer's best quality ratio for each direct quality $u$, the input to Claim 1, Lemma 1(iii) and Proposition 3.
--
--   **Formalization Note.** The domain $[1,\bar t_r)$ is the one of the proof (constraints (16) and $t\ge1$, p. 33). The hypothesis $\bar t_r>1$ says this domain is nonempty; it fails only when $c=0$ and $u\ge\frac1{2k}$. The page's "$t(u)$ is either 1 or …" is rendered as: the maximum is attained, and only at $1$ or $t^L(u)$.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 29, Lemma 1(ii); p. 33, proof of Lemma 1(ii), eqs. (14), (16)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Reduced

namespace QualityEncroach.Differ

theorem lemma_1_ii (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (u : ℝ) (hu : 0 < u)
    (hfeas : 1 < tbarR k c u) :
    (c ≤ (3 * u - 6 * k * u ^ 2) / 4 →
      tL k c u ∈ Set.Ico 1 (tbarR k c u) ∧
      ∀ t ∈ Set.Ico 1 (tbarR k c u), t ≠ tL k c u → PiL k c t u < PiL k c (tL k c u) u) ∧
    ((3 * u - 6 * k * u ^ 2) / 4 < c → c < (4 + 8 * k * u - 23 * k ^ 2 * u ^ 2) / (48 * k) →
      u ≤ 2 / (7 * k) →
      tL k c u ∈ Set.Ico 1 (tbarR k c u) ∧
      (∀ t ∈ Set.Ico 1 (tbarR k c u), PiL k c t u ≤ max (PiL k c 1 u) (PiL k c (tL k c u) u)) ∧
      ∀ t ∈ Set.Ico 1 (tbarR k c u),
        (∀ s ∈ Set.Ico 1 (tbarR k c u), PiL k c s u ≤ PiL k c t u) → t = 1 ∨ t = tL k c u) ∧
    ((3 * u - 6 * k * u ^ 2) / 4 < c →
      ((4 + 8 * k * u - 23 * k ^ 2 * u ^ 2) / (48 * k) ≤ c ∨ 2 / (7 * k) < u) →
      ∀ t ∈ Set.Ico 1 (tbarR k c u), t ≠ 1 → PiL k c t u < PiL k c 1 u) := by sorry

end QualityEncroach.Differ
