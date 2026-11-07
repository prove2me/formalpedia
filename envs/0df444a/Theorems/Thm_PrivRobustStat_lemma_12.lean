-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_12
-- name    : PrivRobustStat.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:34.000557+00:00
-- url     : https://prove2.me/theorems/11de54bb-fec8-4763-80be-aa796e2a96ae
-- title:
--   Lemma 12, p.25 — $\operatorname{Tr}(B\Gamma_p)\le\frac{17\kappa}{30}\operatorname{Tr}(\Gamma_p)$ implies $\operatorname{Tr}(B^q)\le\frac9{10}\Phi$
-- statement:
--   **Lemma 12** (potential decrease). Let $d\ge1$, $p=\lceil\log_2(2d)\rceil$, $q=2p+1$, $\Phi>0$ and $\kappa=\Phi^{1/q}$. Suppose
--
--   $$A\succeq A_1\succeq\cdots\succeq A_p\succeq B\succeq0,\qquad\operatorname{Tr}(A^q)\le\Phi,$$
--
--   and let $\Gamma_0=I$, $\Gamma_j=A_j\Gamma_{j-1}A_j+\eta_jI$ with $0\le d\eta_j\le\frac{\kappa^2}{128p}\operatorname{Tr}(\Gamma_{j-1})$ for $j\in[p]$. If $\operatorname{Tr}(B\Gamma_p)\le\frac{17\kappa}{30}\operatorname{Tr}(\Gamma_p)$, then
--
--   $$\operatorname{Tr}(B^q)\le\tfrac9{10}\Phi.$$
--
--   Differences from the source:
--   - encoding: "Let q, p, Φ, κ be as in Algorithm 1" → d ≥ 1, p = ⌈log₂(2d)⌉, q = 2p + 1, Φ > 0, κ = Φ^{1/q}; reason: Algorithm 1's definitions and input range
--   - encoding: the chain A ⪰ A₁ ⪰ … ⪰ A_p ⪰ B ⪰ 0 → four hypotheses: A − A₁, A_j − A_{j+1} (j < p), A_p − B, B positive semidefinite; reason: the same chain; p ≥ 1 for d ≥ 1
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 12, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_PrivRobustStat_Filter

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 12** (potential decrease), p.25 (PDF p.28).

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let q, p, Φ, κ be as in Algorithm 1. Suppose A ⪰ A₁ ⪰ … ⪰ A_p ⪰ B ⪰ 0_{d×d}, Tr(A^q) ≤ Φ,
Starting from Γ₀ := I, define Γ_j := A_jΓ_{j−1}A_j + η_jI for j ∈ [p], where
0 ≤ dη_j ≤ κ²/(128p) Tr(Γ_{j−1}). Then if, Tr(BΓ_p) ≤ 17κ/30 Tr(Γ_p), we have Tr(B^q) ≤ 9/10 Φ."

**Formalization Note.** As in Algorithm 1: `p = ⌈log₂(2d)⌉` (`pDepth d`, `≥ 1` for `d ≥ 1`),
`q = 2p + 1` (`qExp d`), `Φ > 0` (Algorithm 1's input), `κ = Φ^{1/q}` (`kappaOf d Φ`). The chain
`A ⪰ A₁ ⪰ … ⪰ A_p ⪰ B ⪰ 0` is the four hypotheses `hA`, `hchain`, `hB`, `hB0`; `A_j` are `As j`,
1-based. -/
theorem lemma_12 {d : ℕ} (hd : 1 ≤ d) (Φ : ℝ) (hΦ : 0 < Φ)
    (A B : Matrix (Fin d) (Fin d) ℝ) (As : ℕ → Matrix (Fin d) (Fin d) ℝ) (η : ℕ → ℝ)
    (hA : (A - As 1).PosSemidef)
    (hchain : ∀ j ∈ Finset.Ico 1 (pDepth d), (As j - As (j + 1)).PosSemidef)
    (hB : (As (pDepth d) - B).PosSemidef) (hB0 : B.PosSemidef)
    (htr : Matrix.trace (A ^ qExp d) ≤ Φ)
    (hη : ∀ j ∈ Finset.Icc 1 (pDepth d), 0 ≤ (d : ℝ) * η j ∧
      (d : ℝ) * η j ≤ kappaOf d Φ ^ 2 / (128 * (pDepth d : ℝ)) *
        Matrix.trace (gammaSeq As η (j - 1)))
    (hcond : Matrix.trace (B * gammaSeq As η (pDepth d)) ≤
      17 * kappaOf d Φ / 30 * Matrix.trace (gammaSeq As η (pDepth d))) :
    Matrix.trace (B ^ qExp d) ≤ 9 / 10 * Φ := by sorry

end PrivRobustStat
