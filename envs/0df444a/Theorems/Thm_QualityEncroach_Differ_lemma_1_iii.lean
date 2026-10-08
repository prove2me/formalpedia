-- Prove2me | Theorems.Thm_QualityEncroach_Differ_lemma_1_iii
-- name    : QualityEncroach.Differ.lemma_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:47.130379+00:00
-- url     : https://prove2.me/theorems/451dafa8-d57b-4be1-ad05-f9d35e11e327
-- title:
--   Lemma 1(iii), p. 29 — for c < 1/(12k), a unique ũ(c) at which high- and low-quality encroachment profits cross
-- statement:
--   Fix $k>0$ and $0\le c<\frac1{12k}$, and let $\Pi^H_M(u)$ and $\Pi^L_M(u)$ be the manufacturer's profits under high-quality encroachment (ratio $t^H(u)<1$ of Lemma 1(i)) and low-quality encroachment (ratio $t^L(u)>1$ of Lemma 1(ii)). Write
--
--   $$
--   \underline u=\sqrt{\tfrac{4c}{3k}},\qquad \bar u=\frac{3+\sqrt{3(3-32kc)}}{12k}.
--   $$
--
--   There is a unique $\tilde u(c)\in(\underline u,\bar u)$ such that
--
--   $$
--   \Pi^L_M(u)>\Pi^H_M(u)\ \text{ for } \underline u<u<\tilde u(c),
--   \qquad
--   \Pi^H_M(u)>\Pi^L_M(u)\ \text{ for } \tilde u(c)<u<\bar u .
--   $$
--
--   In the paper's words: for given $u$ in this interval, the optimal ratio exceeds $1$ below $\tilde u(c)$ and is below $1$ above it.
--
--   **Formalization Note.** The page phrases the conclusion through the optimal ratio $t(u)$; the proof (p. 30) establishes it as the crossing of $\Pi^H_M$ and $\Pi^L_M$, which is what is stated. At $u=\tilde u(c)$ the two profits are equal; the page's "$t(u)<1$ if $\tilde u(c)\le u$" includes that point, where both ratios are optimal, so the point is left out. At $c=0$ the left endpoint is $u=0$, outside the positive-quality domain, but the threshold remains in the open interval.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 29, Lemma 1(iii) (proof: pp. 29–30)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Reduced

namespace QualityEncroach.Differ

theorem lemma_1_iii (k c : ℝ) (hk : 0 < k) (hc0 : 0 ≤ c) (hc1 : c < 1 / (12 * k)) :
    ∃! ut : ℝ,
      ut ∈ Set.Ioo (Real.sqrt (4 * c / (3 * k))) ((3 + Real.sqrt (3 * (3 - 32 * k * c))) / (12 * k)) ∧
      PiHu k c ut = PiLu k c ut ∧
      (∀ u ∈ Set.Ioo (Real.sqrt (4 * c / (3 * k))) ut, PiHu k c u < PiLu k c u) ∧
      (∀ u ∈ Set.Ioo ut ((3 + Real.sqrt (3 * (3 - 32 * k * c))) / (12 * k)),
        PiLu k c u < PiHu k c u) := by sorry

end QualityEncroach.Differ
