-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_11
-- name    : PrivRobustStat.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:01.35712+00:00
-- url     : https://prove2.me/theorems/4a043316-8019-449d-bf5b-490dc8c24233
-- title:
--   Lemma 11, p.25 — $\operatorname{Tr}(\Gamma_p)\le d^{1/q}e^{d^{2/q}/128}\kappa^{q-1}$ (and $d^{1/q}\kappa^{q-1}$ without noise)
-- statement:
--   **Lemma 11.** Let $p\in\mathbb N$, $q=2p+1$, $\kappa\ge0$, and let $A_1,\dots,A_p$ be positive semidefinite with $\operatorname{Tr}(A_j^q)\le\kappa^q$. Define $\Gamma_0=I$ and $\Gamma_j=A_j\Gamma_{j-1}A_j+\eta_jI$, where $0\le d\eta_j\le\frac{\kappa^2}{128p}\operatorname{Tr}(\Gamma_{j-1})$ for $j\in[p]$. Then
--
--   $$\operatorname{Tr}(\Gamma_p)\le d^{1/q}\exp\Big(\frac{d^{2/q}}{128}\Big)\kappa^{q-1},$$
--
--   and if $\eta_j=0$ for all $j$, then $\operatorname{Tr}(\Gamma_p)\le d^{1/q}\kappa^{q-1}$.
--
--   This is the upper bound comparison in the potential argument.
--
--   Differences from the source:
--   - generalization: p ∈ N → p ∈ ℕ including p = 0; reason: at p = 0 the claim is Tr I = d ≤ d·e^{d²/128}, true; for p ≥ 1 it is the source
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 11, p.25 (PDF p.28); proof in Appendix A.1, pp.74–75

import Mathlib
import Definitions.Def_PrivRobustStat_Model

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 11**, p.25 (PDF p.28); proof in Appendix A.1, pp.74–75.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let p ∈ N, q = 2p + 1, and κ ≥ 0. Let A[p] ⊂ S^{d×d}_{⪰0} satisfy Tr(A_j^q) ≤ κ^q for j ∈ [p].
Define Γ₀ := I and Γ_j := A_jΓ_{j−1}A_j + η_jI, where 0 ≤ dη_j ≤ κ²/(128p) Tr(Γ_{j−1}) for j ∈ [p].
Then, Tr(Γ_p) ≤ d^{1/q} exp(d^{2/q}/128) κ^{q−1}. If η_j = 0 for all j ∈ [p], then
Tr(Γ_p) ≤ d^{1/q} κ^{q−1}."

**Formalization Note.** `Γ` is `gammaSeq A η` (1-based `A j`, `η j`); `q = 2p + 1` is written out,
so `κ^{q−1} = κ^{2p}`. `d^{1/q}` and `d^{2/q}` are real powers. `p = 0` is allowed (then the claim
is `Tr I = d ≤ d·e^{d²/128}`). -/
theorem lemma_11 {d : ℕ} (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (η : ℕ → ℝ) (hpsd : ∀ j ∈ Finset.Icc 1 p, (A j).PosSemidef)
    (htr : ∀ j ∈ Finset.Icc 1 p, Matrix.trace (A j ^ (2 * p + 1)) ≤ κ ^ (2 * p + 1))
    (hη : ∀ j ∈ Finset.Icc 1 p, 0 ≤ (d : ℝ) * η j ∧
      (d : ℝ) * η j ≤ κ ^ 2 / (128 * (p : ℝ)) * Matrix.trace (gammaSeq A η (j - 1))) :
    Matrix.trace (gammaSeq A η p) ≤
        (d : ℝ) ^ ((1 : ℝ) / (2 * p + 1)) * Real.exp ((d : ℝ) ^ ((2 : ℝ) / (2 * p + 1)) / 128) *
          κ ^ (2 * p) ∧
      ((∀ j ∈ Finset.Icc 1 p, η j = 0) →
        Matrix.trace (gammaSeq A η p) ≤ (d : ℝ) ^ ((1 : ℝ) / (2 * p + 1)) * κ ^ (2 * p)) := by sorry

end PrivRobustStat
