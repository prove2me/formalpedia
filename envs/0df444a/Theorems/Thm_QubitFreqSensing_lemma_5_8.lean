-- Prove2me | Theorems.Thm_QubitFreqSensing_lemma_5_8
-- name    : QubitFreqSensing.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:58.798335+00:00
-- url     : https://prove2.me/theorems/792f58ec-9b8a-4091-bb58-a6cc0a41e4c5
-- title:
--   Lemma 5.8 — rescaling to $\|u\|^2=1/(2C)$ does not decrease $J$; maximizers satisfy $\|u\|^2\le1/(2C)$
-- statement:
--   Let $N\ge1$, $\omega_1,\dots,\omega_N>0$ and $C>0$. The lemma has three parts.
--
--   1. If $u\in\mathbb T$ satisfies $\|u\|^2>1/(2C)$, then
--   $$
--   J\Bigl(\frac1{\sqrt{2C}}\,\frac{u}{\|u\|}\Bigr)\ \ge\ J(u).
--   $$
--   2. If moreover $J(u)>-\infty$, the inequality is strict.
--   3. Every maximizer $u$ of $J$ over $\mathbb T$ satisfies $\|u\|^2\le 1/(2C)$.
--
--   Here $\|u\|^2=\langle u,u\rangle=\frac1{2\pi}\int_0^{2\pi}|u|^2$. The norm bound feeds the slope estimate in Lemma 5.9.
--
--   Differences from the source:
--   - encoding: J : 𝕋 → ℝ ∪ {−∞} with log 0 = −∞ → J valued in EReal, penalty via a lower Lebesgue integral; reason: Lean's Real.log 0 = 0 and non-integrable Bochner integrals = 0 would hide −∞
--   - encoding: 𝕋 = L² functions [0, 2π] → 𝔻 → measurable u : ℝ → ℂ with ‖u x‖ < 1 on [0, 2π] (discFns); reason: every quantity depends only on the a.e. class (a Lebesgue-measurable u agrees a.e. with a Borel one, changed to 0 on a null set); L² is automatic for |u| < 1
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Lemma 5.8, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_QubitFreqSensing_Potential

namespace QubitFreqSensing

/-- **Lemma 5.8** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), Lemma 5.8,
p.18). "Suppose u ∈ 𝕋 satisfies ∥u∥² > 1/(2C). Then, J((1/√(2C)) · u/∥u∥) ≥ J(u). The inequality is
strict whenever J(u) is finite. In particular, every maximizer u of J satisfies ∥u∥² ≤ 1/(2C)."

All three clauses: (1) the inequality, (2) strictness when `J(u) ≠ −∞`, (3) every maximizer of `J`
over `𝕋` has `‖u‖² ≤ 1/(2C)`.

**Formalization Note** `‖u‖² = ⟨u, u⟩` with the `1/2π` normalization (`normSq2pi`), and
`‖u‖ = √⟨u, u⟩`. The standing assumptions of §5 (`N ≥ 1`, `ω_i > 0`) and `C > 0` (p.18) are
hypotheses. -/
theorem lemma_5_8 (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → ℝ) (hω : ∀ i, 0 < ω i)
    (C : ℝ) (hC : 0 < C) :
    (∀ u ∈ discFns, 1 / (2 * C) < normSq2pi u →
      J C ω u ≤ J C ω (fun x => ((1 / (Real.sqrt (2 * C) * Real.sqrt (normSq2pi u)) : ℝ) : ℂ) * u x)
      ∧ (J C ω u ≠ ⊥ →
        J C ω u < J C ω (fun x => ((1 / (Real.sqrt (2 * C) * Real.sqrt (normSq2pi u)) : ℝ) : ℂ) * u x)))
    ∧ (∀ u ∈ discFns, (∀ v ∈ discFns, J C ω v ≤ J C ω u) → normSq2pi u ≤ 1 / (2 * C)) := by sorry

end QubitFreqSensing
