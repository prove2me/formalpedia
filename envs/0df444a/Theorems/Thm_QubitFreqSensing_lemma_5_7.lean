-- Prove2me | Theorems.Thm_QubitFreqSensing_lemma_5_7
-- name    : QubitFreqSensing.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:48.364667+00:00
-- url     : https://prove2.me/theorems/5f4d8f48-8c27-447d-91ef-5c665c4d79fc
-- title:
--   Lemma 5.7 — $J$ attains a finite maximum on $\mathbb T$
-- statement:
--   Let $N\ge1$, $\omega_1,\dots,\omega_N>0$ and $C>0$, and let $J$ be the potential (13). Then there is $u\in\mathbb T$ with $J(u)>-\infty$ and
--
--   $$
--   J(v)\le J(u)\qquad\text{for all } v\in\mathbb T .
--   $$
--
--   The maximizer is the starting point of the proof of Theorem 5.1: by Lemma 5.8 it has small norm, and by Corollary 5.10 none of its correlations can be small.
--
--   Differences from the source:
--   - encoding: 𝕋 = L² functions [0, 2π] → 𝔻 → measurable u : ℝ → ℂ with ‖u x‖ < 1 on [0, 2π] (discFns); reason: every quantity depends only on the a.e. class; L² is automatic for |u| < 1
--   - encoding: a finite maximum → J u ≠ ⊥ (J ≤ 0 always); reason: EReal convention
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Lemma 5.7, p.18 (PDF p.18); proof in App. A, pp.33–34

import Mathlib
import Definitions.Def_QubitFreqSensing_Potential

namespace QubitFreqSensing

/-- **Lemma 5.7** (existence of a maximizer; Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027
submission), Lemma 5.7, p.18, proved in App. A, pp.33–34). "For every C > 0, the functional J
attains a finite maximum on 𝕋."

**Formalization Note** `J` is `EReal`-valued and `≤ 0`; "finite" is `J u ≠ ⊥`. The standing
assumptions of §5 (`N ≥ 1`, `ω_i > 0`, Theorem 5.1, p.16) are hypotheses. -/
theorem lemma_5_7 (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → ℝ) (hω : ∀ i, 0 < ω i)
    (C : ℝ) (hC : 0 < C) :
    ∃ u ∈ discFns, J C ω u ≠ ⊥ ∧ ∀ v ∈ discFns, J C ω v ≤ J C ω u := by sorry

end QubitFreqSensing
