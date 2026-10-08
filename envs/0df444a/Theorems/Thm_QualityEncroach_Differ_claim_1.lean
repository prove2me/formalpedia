-- Prove2me | Theorems.Thm_QualityEncroach_Differ_claim_1
-- name    : QualityEncroach.Differ.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:51.638646+00:00
-- url     : https://prove2.me/theorems/8625ff89-cb97-465b-9a3e-395a5c232418
-- title:
--   Claim 1, p. 30 — dΠ^H_M(u)/du > dΠ^L_M(u)/du on [√(4c/(3k)), (3 + √(3(3 − 32kc)))/(12k)]
-- statement:
--   Fix $k>0$ and a direct selling cost $0\le c<\frac1{12k}$. Let $\Pi^H_M(u)=\Pi^H(t^H(u),u)$ be the manufacturer's profit under high-quality encroachment at the ratio $t^H(u)=\frac65-\frac25\sqrt{4-\frac{5c}{ku^2}}$ of Lemma 1(i), and $\Pi^L_M(u)=\Pi^L(t^L(u),u)$ her profit under low-quality encroachment at the ratio $t^L(u)=\frac{2+5ku+\sqrt{4-48kc+8ku-23k^2u^2}}{12ku}$ of Lemma 1(ii) (with $\Pi^H$, $\Pi^L$ the reduced profits of pp. 29 and 33). Then
--
--   $$
--   \frac{d\Pi^H_M(u)}{du}>\frac{d\Pi^L_M(u)}{du}
--   \qquad\text{for all } u>0\text{ in }\Bigl[\sqrt{\tfrac{4c}{3k}},\ \tfrac{3+\sqrt{3(3-32kc)}}{12k}\Bigr].
--   $$
--
--   The interval is the set of qualities at which both differentiated ratios beat uniform quality; the claim yields the single crossing of Lemma 1(iii).
--
--   **Formalization Note.** Claim 1 sits inside the proof of Lemma 1(iii), which assumes $c<\frac1{12k}$ (the interval is nonempty exactly then). At $c=0$ the interval begins at $u=0$, outside the paper's positive-quality domain; the statement only quantifies over $u>0$.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 30, Claim 1 (proof: pp. 33–34)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Reduced

namespace QualityEncroach.Differ

theorem claim_1 (k c : ℝ) (hk : 0 < k) (hc0 : 0 ≤ c) (hc1 : c < 1 / (12 * k)) :
    ∀ u ∈ Set.Icc (Real.sqrt (4 * c / (3 * k))) ((3 + Real.sqrt (3 * (3 - 32 * k * c))) / (12 * k)),
      0 < u → deriv (PiLu k c) u < deriv (PiHu k c) u := by sorry

end QualityEncroach.Differ
