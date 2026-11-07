-- Prove2me | Theorems.Thm_QubitFreqSensing_corollary_5_10
-- name    : QubitFreqSensing.corollary_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:12.441203+00:00
-- url     : https://prove2.me/theorems/5db88028-0061-4c56-a387-dc40c257b2b2
-- title:
--   Corollary 5.10 — a random Möbius perturbation raises $J$ by $\frac12\log2$ in expectation
-- statement:
--   Let $N\ge1$, $\omega_1,\dots,\omega_N>0$, $C\ge4$, $\eta\in(0,1/16)$ with $4C\eta^2<\log 2$, and $c\le\eta/32$. Put $r=\eta/\sqrt N$. Let $u\in\mathbb T$ with $\|u\|^2\le1/(2C)$ and $J(u)>-\infty$, and suppose $|\langle g_i,u\rangle|<c/\sqrt N$ for some $i$. Then $J(\Phi^{(i)}_z u)>-\infty$ for almost every $z$ on the circle $|z|=r$, and
--
--   $$
--   \mathbb E_{|z|=r}\Bigl[J\bigl(\Phi^{(i)}_z(u)\bigr)-J(u)\Bigr]\ \ge\ \frac12\log 2, \tag{14}
--   $$
--
--   where $\mathbb E_{|z|=r}$ averages over $z=re^{i\theta}$ with $\theta$ uniform in $[0,2\pi]$. Applied to a maximizer of $J$, this shows that no correlation of the maximizer is below $c/\sqrt N$, which proves Theorem 5.1.
--
--   Differences from the source:
--   - reading: C > 0 'sufficiently large' and r = η/√N with 4Cη² < log 2 → C ≥ 4 and η ∈ (0, 1/16) in addition to 4Cη² < log 2; reason: the proof applies Lemma 5.9, whose η lies in (0, 1/16), and 'where we used that C ≥ 4' (p.20); Theorem 5.11 says 'Let C, r, η, and c be as in the previous subsection'
--   - encoding: |⟨g_i, u⟩| < c/√N, which allows ⟨g_i, u⟩ = 0 → adds J(u) ≠ −∞; reason: for J(u) = −∞ the expectation of J(Φ_z u) − J(u) is the undefined −∞ − (−∞)
--   - generalization: E_{|z|=r}[J(Φ_z^{(i)}(u)) − J(u)] ≥ ½ log 2 → also J(Φ_z^{(i)} u) ≠ −∞ for a.e. θ, and the average is of real differences (EReal.toReal); reason: the extra clause makes the real-valued average the paper's expectation; it holds because J(Φ_z u) − J(u) is bounded below by integrable functions of z
--   - encoding: J : 𝕋 → ℝ ∪ {−∞} with log 0 = −∞ → J valued in EReal, penalty via a lower Lebesgue integral; reason: Lean's Real.log 0 = 0 and non-integrable Bochner integrals = 0 would hide −∞
--   - encoding: 𝕋 = L² functions [0, 2π] → 𝔻 → measurable u : ℝ → ℂ with ‖u x‖ < 1 on [0, 2π] (discFns); reason: every quantity depends only on the a.e. class (a Lebesgue-measurable u agrees a.e. with a Borel one, changed to 0 on a null set); L² is automatic for |u| < 1
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Corollary 5.10, p.20 (PDF p.20); proof p.21

import Mathlib
import Definitions.Def_QubitFreqSensing_Potential
import Definitions.Def_QubitFreqSensing_Mobius

open MeasureTheory Real

namespace QubitFreqSensing

/-- **Corollary 5.10** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), Corollary
5.10, p.20). "Let u ∈ 𝕋 be so that ∥u∥² ≤ 1/(2C) and |⟨gi, u⟩| < c/√N for some i. Let r = η/√N,
where η satisfies 4Cη² < log 2, and c satisfies c ≤ η/32. Then, we have that
E_{|z|=r}[J(Φz^{(i)}(u)) − J(u)] ≥ (1/2) log 2. (14)"

The conclusion has two parts: `J(Φ_z^{(i)} u)` is finite for almost every `z` on the circle
`|z| = r`, and the circle average of `J(Φ_z^{(i)} u) − J(u)` is at least `½ log 2`.

**Formalization Note** `E_{|z|=r}` is `Real.circleAverage · 0 r` (uniform `θ ∈ [0, 2π]`,
`z = r e^{iθ}`, p.19). The constants are those of Lemma 5.9, whose proof this corollary applies:
`C ≥ 4` ("where we used that C ≥ 4", p.20) and `η ∈ (0, 1/16)` (Lemma 5.9's `η`). `J(u) ≠ −∞`
excludes the undefined difference `−∞ − (−∞)`. Since `J ≤ 0`, the a.e. finiteness clause makes the
`EReal.toReal` differences the genuine values. The standing assumptions of §5 (`N ≥ 1`, `ω_i > 0`)
are hypotheses. -/
theorem corollary_5_10 (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → ℝ) (hω : ∀ i, 0 < ω i)
    (C η c : ℝ) (hC : 4 ≤ C) (hη0 : 0 < η) (hη1 : η < 1 / 16)
    (hCη : 4 * C * η ^ 2 < Real.log 2) (hc : c ≤ η / 32)
    (u : ℝ → ℂ) (hu : u ∈ discFns) (hnorm : normSq2pi u ≤ 1 / (2 * C))
    (i : Fin N) (hi : ‖inner2pi (gcos ω i) u‖ < c / Real.sqrt N) (hJ : J C ω u ≠ ⊥) :
    (∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * π))),
        J C ω (Phi ω i (circleMap 0 (η / Real.sqrt N) θ) u) ≠ ⊥) ∧
      Real.log 2 / 2 ≤ Real.circleAverage
        (fun z => (J C ω (Phi ω i z u)).toReal - (J C ω u).toReal) 0 (η / Real.sqrt N) := by sorry

end QubitFreqSensing
