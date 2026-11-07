-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_16
-- name    : PrivRobustStat.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:09.040241+00:00
-- url     : https://prove2.me/theorems/df9623a7-98de-4cde-b534-47175d1426de
-- title:
--   Lemma 16, p.34 — $\|\hat\mu(w)-\hat\mu(w_G)\|_2^2\le2\alpha\|\hat\Sigma(w)-\hat\Sigma(w_G)\|_{\mathrm{op}}$
-- statement:
--   **Lemma 16.** Let $x_{[n]}\subset\mathbb R^d$, let $G\subseteq[n]$ and $B=[n]\setminus G$, and let $w\in\mathcal W$ satisfy $\|w_G\|_1\ge\tfrac34$ and $\|w_B\|_1\le\alpha$. Then
--
--   $$\|\hat\mu(w)-\hat\mu(w_G)\|_2^2\le2\alpha\,\|\hat\Sigma(w)-\hat\Sigma(w_G)\|_{\mathrm{op}}.$$
--
--   It controls the shift of the centre caused by bad weight, which the proof of Theorem 4 uses to verify Item (b) of Proposition 1.
--
--   **Formalization Note** $\|\cdot\|_{\mathrm{op}}$ is the published operator norm of a symmetric matrix; $\hat\Sigma(\cdot)$ is centred at its own weighted mean.
--
--   Differences from the source:
--   - encoding: ∥·∥_op → HighDimStat.Pca.opNormSymm, sup over unit vectors of |⟨v, Av⟩|; reason: equals the operator norm on symmetric matrices, and Σ̂(w) − Σ̂(w_G) is symmetric
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 16, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_PrivRobustStat_Model
import Definitions.Def_HighDimStat_Pca_OpNormSymm

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 16**, p.34 (PDF p.37).

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let w ∈ W satisfy ∥w_G∥₁ ≥ 3/4 and ∥w_B∥₁ ≤ α. Then ∥µ̂(w) − µ̂(w_G)∥₂² ≤ 2α∥Σ̂(w) − Σ̂(w_G)∥_op."

**Formalization Note.** `G` is any set of indices and `B := [n] \ G` (`Gᶜ`); `α` is any real (the
hypotheses force `α ≥ 0`). `w_G = restrict w G`; `Σ̂(·)` is centred at its own weighted mean
(`cov`); `∥·∥_op` is `HighDimStat.Pca.opNormSymm` applied to the symmetric matrix
`Σ̂(w) − Σ̂(w_G)`. -/
theorem lemma_16 {d n : ℕ} (x : Fin n → Vec d) (G : Finset (Fin n)) (α : ℝ) (w : Fin n → ℝ)
    (hw : InW n w) (hG : 3 / 4 ≤ l1 (restrict w G)) (hB : l1 (restrict w Gᶜ) ≤ α) :
    ‖wMean x w - wMean x (restrict w G)‖ ^ 2 ≤
      2 * α * HighDimStat.Pca.opNormSymm (cov x w - cov x (restrict w G)) := by sorry

end PrivRobustStat
