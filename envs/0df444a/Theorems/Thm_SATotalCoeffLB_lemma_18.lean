-- Prove2me | Theorems.Thm_SATotalCoeffLB_lemma_18
-- name    : SATotalCoeffLB.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:26.164292+00:00
-- url     : https://prove2.me/theorems/19d08810-1058-42ca-bc07-bc158bba8369
-- title:
--   Lemma 18 — quadratic phase bound $|\mathbb E_{\bar x}(-1)^{\alpha\cdot\bar x+b(\bar x)}|\le 2^{-\mathrm{rank}(b)/2}$
-- statement:
--   For every $b \in Q_n$ and $\alpha \in \mathbb F_2^n$,
--
--   $$
--   \Bigl| \mathbb E_{\bar x \in \mathbb F_2^n} (-1)^{\alpha\cdot\bar x + b(\bar x)} \Bigr| \le 2^{-\operatorname{rank}(b)/2},
--   $$
--
--   where $\operatorname{rank}(b)$ is the $\mathbb F_2$-rank of the polar matrix $B_b$ (Definition 3).
--
--   This bound gives property 4 of Lemma 17: monomial multiples of $A_e$ have value $O(2^{-\tau n/2})$ under $L_0$ because they only involve forms of rank above $\tau n - 2$.
--
--   **Formalization Note** The absolute value is on the rendered page; the PDF text layer drops the bars. The exponent $-\operatorname{rank}(b)/2$ is a real number.
--
--   Differences from the source:
--   - encoding: $\mathbb E_{\bar x \in \mathbb F_2^n}$ and $(-1)^{\alpha\cdot\bar x + b(\bar x)}$ → $2^{-n}\sum_{\bar x}$ and $(-1)^{\mathrm{val}(\alpha\cdot\bar x + b(\bar x))}$; reason: same value
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Lemma 18, p.53

import Mathlib
import Definitions.Def_SATotalCoeffLB_phaseExp
import Definitions.Def_SATotalCoeffLB_qrank

namespace SATotalCoeffLB

/-- **Lemma 18 (quadratic phase bound)**, p.53 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

For every quadratic form `b ∈ Q_n` and every `α ∈ F₂ⁿ`,
`|E_{x̄ ∈ F₂ⁿ} (−1)^{α·x̄ + b(x̄)}| ≤ 2^{−rank(b)/2}`.

**Formalization Note** The absolute value is on the rendered page (the text layer drops it). The
exponent `rank(b)/2` is real (`Real.rpow`). -/
theorem lemma_18 (n : ℕ) (b : QForm n) (α : Fin n → ZMod 2) :
    |phaseExp α b| ≤ (2 : ℝ) ^ (-((qrank b : ℝ) / 2)) := by sorry

end SATotalCoeffLB
