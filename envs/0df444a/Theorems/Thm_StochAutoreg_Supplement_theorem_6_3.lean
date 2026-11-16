-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_6_3
-- name    : StochAutoreg.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:25:58.935198+00:00
-- url     : https://prove2.me/theorems/4aa388bb-0248-4171-ac84-00abf6962a7d
-- title:
--   Theorem 6.3 — a finite class with $m_{\mathrm{base}}(C\varepsilon/M)=0$ but $m_{\mathrm{CoT}}(\varepsilon)\ge cK/\varepsilon$
-- statement:
--   There are universal constants $c,C,\varepsilon_0>0$ such that, for every $K\ge1$, every integer $M\ge2$ and every $0<\varepsilon\le\varepsilon_0$, a finite class $\mathcal F$ satisfies
--
--   $$m^{\mathcal F}_{\mathrm{base}}(C\varepsilon/M)=0,\qquad m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon)\ge cK/\varepsilon .$$
--
--   Consequently, for fixed $0<\beta<1$ the base sample complexity of the same class is also zero at accuracy $\varepsilon^{1-\beta}/M$ for sufficiently small $\varepsilon$ (namely when $C\varepsilon^\beta\le1$), and at accuracy $\varepsilon/M^{1-\beta}$ for sufficiently large $M$ (namely when $C\le M^\beta$). All complexities are at confidence $2/3$.
--
--   This shows that the accuracy $\varepsilon/M$ in Theorem 5.1 is necessary up to the constant: the base problem can be trivial at accuracy $C\varepsilon/M$ while chain-of-thought learning needs arbitrarily many samples.
--
--   **Formalization Note** The lower bound holds for every finite value of $m_{\mathrm{CoT}}(\varepsilon)$, and trivially when it is $+\infty$.
--
--   Differences from the source:
--   - encoding: m(ε) with δ omitted → m(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - encoding: m_CoT(ε) ≥ cK/ε with m_CoT ∈ {0,…,+∞} → c·K/ε ≤ n for every finite value n of m_CoT(ε); reason: the value +∞ satisfies the lower bound
--   - reading: K ≥ 1 (type not stated) → K real, K ≥ 1; reason: the stronger of the two readings; the proof takes ⌈K⌉ roots
--   - generalization: "for sufficiently small ε" / "for sufficiently large M" → whenever C·ε^β ≤ 1, resp. whenever C ≤ M^β; reason: explicit thresholds ε ≤ C^{−1/β} and M ≥ C^{1/β}, depending on β only; they come from the proof's comparison with Cε/M and imply the existence of the thresholds
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 6.3, p.13

import Mathlib
import Definitions.Def_StochAutoreg_mBase
import Definitions.Def_StochAutoreg_mCoT

namespace StochAutoreg

namespace Supplement

/-- **Theorem 6.3** (the accuracy `ε/M` in Theorem 5.1). There are universal `c, C, ε₀ > 0` such that,
for every `K ≥ 1`, `M ≥ 2` and `0 < ε ≤ ε₀`, a finite class satisfies `m^F_base(Cε/M) = 0` and
`m^{F,M}_CoT(ε) ≥ cK/ε`. Consequently, for fixed `0 < β < 1` the base sample complexity is also zero at
accuracy `ε^{1−β}/M` for sufficiently small `ε`, and at `ε/M^{1−β}` for sufficiently large `M`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 6.3, p.13.

**Formalization Note.** Confidence `δ = 1/3` throughout. `K` is real (the stronger reading; the
proof uses `⌈K⌉` roots). The lower bound is stated for every finite value of `m_CoT(ε)`, so
`m_CoT(ε) = +∞` satisfies it. The consequence is about the same class, with the thresholds that the
proof's comparison with `Cε/M` gives: `ε^{1−β}/M ≥ Cε/M` exactly when `Cε^β ≤ 1`, and
`ε/M^{1−β} ≥ Cε/M` exactly when `C ≤ M^β`. -/
theorem theorem_6_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ K : ℝ, 1 ≤ K → ∀ M : ℕ, 2 ≤ M → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ F : Set Generator, F.Finite ∧
          mBase F (C * ε / M) (1 / 3) = 0 ∧
          (∀ n : ℕ, mCoT F M ε (1 / 3) = n → c * K / ε ≤ n) ∧
          ∀ β : ℝ, 0 < β → β < 1 →
            (C * ε ^ β ≤ 1 → mBase F (ε ^ (1 - β) / M) (1 / 3) = 0) ∧
            (C ≤ (M : ℝ) ^ β → mBase F (ε / (M : ℝ) ^ (1 - β)) (1 / 3) = 0) := by sorry

end Supplement

end StochAutoreg
