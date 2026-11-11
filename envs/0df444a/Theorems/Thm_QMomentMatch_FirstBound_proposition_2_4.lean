-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_proposition_2_4
-- name    : QMomentMatch.FirstBound.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:59:49.968355+00:00
-- url     : https://prove2.me/theorems/94b3a108-3b59-475c-9130-969f69dfecce
-- title:
--   Proposition 2.4 — normalization of moments
-- statement:
--   Let $A\ge1$ and let $X_0,X_1$ be positive frequency statistics supported on $[A]$, with means $\mu_b=\mathbb E[X_b]$ and mean-one statistics $Z_b$ defined by (4). Then for $b\in\{0,1\}$ and every integer $j\ge1$,
--   $$\mathbb E[Z_b^j]=\frac{\mathbb E[X_b^j]}{\mu_b},\qquad \mathbb E[Z_b]=1,$$
--   and consequently, for every integer $j\ge1$,
--   $$\mathbb E[Z_0^j]=\mathbb E[Z_1^j]\iff\frac{\mathbb E[X_1^j]}{\mathbb E[X_0^j]}=\frac{\mu_1}{\mu_0}.$$
--
--   This turns the proportional-moment hypothesis (7) on the positive statistics into exact matching of the first $r-1$ moments of the mean-one statistics, which is what the hybrid argument consumes.
--
--   **Formalization Note** Laws on $S=\{0,\dots,A\}$ are probability vectors on `Fin (A + 1)`; positive statistics put no mass on $0$.
--
--   Differences from the source:
--   - reading: "positive frequency statistics $X$ supported on $[A]$" → any probability vector on $\{1,\dots,A\}$ (written on $\{0,\dots,A\}$ with no mass at $0$); reason: the statement uses only the law of $X$, and every such law is allowed in Definition 2.1.
--   - encoding: $S=\{0\}\cup[A]$ → `Fin (A + 1)`; reason: index convention, same laws and moments.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Proposition 2.4, p. 13

import Mathlib
import Definitions.Def_QMomentMatch_FirstBound_Basic

namespace QMomentMatch.FirstBound

/-- Proposition 2.4 (Normalization of moments), p. 13. -/
theorem proposition_2_4 (A : ℕ) (hA : 1 ≤ A) (X₀ X₁ : Fin (A + 1) → ℝ)
    (hX₀ : IsPosFreqStat X₀) (hX₁ : IsPosFreqStat X₁) :
    (∀ X ∈ ({X₀, X₁} : Set (Fin (A + 1) → ℝ)),
      (∀ j : ℕ, 1 ≤ j → moment (meanOne X) j = moment X j / moment X 1) ∧
        moment (meanOne X) 1 = 1) ∧
    ∀ j : ℕ, 1 ≤ j →
      (moment (meanOne X₀) j = moment (meanOne X₁) j ↔
        moment X₁ j / moment X₀ j = moment X₁ 1 / moment X₀ 1) := by sorry

end QMomentMatch.FirstBound
