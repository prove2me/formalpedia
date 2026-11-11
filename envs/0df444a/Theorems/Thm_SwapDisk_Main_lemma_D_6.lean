-- Prove2me | Theorems.Thm_SwapDisk_Main_lemma_D_6
-- name    : SwapDisk.Main.lemma_D_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:16:23.296469+00:00
-- url     : https://prove2.me/theorems/a751a54a-0e55-4ea6-a153-18cab58dbc74
-- title:
--   Lemma D.6 — absolute displacement of the simple random walk: $m_T=T2^{-(T-1)}\binom{T-1}{\lfloor (T-1)/2\rfloor}\ge\sqrt{T/2}$, equality at $T=2$
-- statement:
--   For independent uniform signs $\varepsilon_1,\dots,\varepsilon_T$ let $m_T=\mathbb E|\sum_t\varepsilon_t|$. For every integer $T\ge1$,
--   $$m_T=T\,2^{-(T-1)}\binom{T-1}{\lfloor(T-1)/2\rfloor}\ge\sqrt{T/2},$$
--   and the constant $1/\sqrt2$ in this uniform comparison is attained at $T=2$ ($m_2=1=\sqrt{2/2}$).
--
--   This is the size of the statistical lower bound.
--
--   Differences from the source:
--   - encoding: m_T = E|∑ ε_t| for independent uniform signs → `KhintchineTwoRegime.K T (fun _ => 1)`: the uniform average over `Fin T → Bool`; reason: the expectation of a function of finitely many fair signs is this average
--   - encoding: the constant 1/√2 is attained at T = 2 → m_2 = √(2/2); reason: m_T/√T = 1/√2 at T = 2
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 45, Lemma D.6

import Mathlib
import Definitions.Def_SwapDisk_Main_Geometry

namespace SwapDisk.Main

/-- Lemma D.6 (Absolute displacement of the simple random walk), p. 45: for every integer
`T ≥ 1`, `m_T = T 2^{−(T−1)} C(T−1, ⌊(T−1)/2⌋) ≥ √(T/2)`; the constant `1/√2` is attained at
`T = 2` (`m_2 = √(2/2)`). -/
theorem lemma_D_6 :
    (∀ T : ℕ, 1 ≤ T →
      mT T = (T : ℝ) * ((T - 1).choose ((T - 1) / 2) : ℝ) / (2 : ℝ) ^ (T - 1) ∧
      Real.sqrt ((T : ℝ) / 2) ≤ mT T) ∧
    mT 2 = Real.sqrt ((2 : ℝ) / 2) := by sorry

end SwapDisk.Main
