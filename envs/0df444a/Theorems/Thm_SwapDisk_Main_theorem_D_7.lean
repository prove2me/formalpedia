-- Prove2me | Theorems.Thm_SwapDisk_Main_theorem_D_7
-- name    : SwapDisk.Main.theorem_D_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:57.852113+00:00
-- url     : https://prove2.me/theorems/d39cb7eb-a11b-4e31-adb0-560543977092
-- title:
--   Theorem D.7 — statistical obstruction: against $D_{\mathrm{sign}}$ every learner has $\mathbb ER_T\ge m_T$, $\mathbb P\{R_T\ge m_T/2\}\ge m_T^2/(16T)\ge1/32$; $V_T\ge m_T\ge\sqrt{T/2}$
-- statement:
--   Let $T\ge2$ and let $D_{\mathrm{sign}}$ play $g_t=\varepsilon_te_1$ with independent uniform signs. Every admissible learner $A$ satisfies
--   $$\mathbb E_{A,D_{\mathrm{sign}}}R_T\ge m_T,\qquad\mathbb P_{A,D_{\mathrm{sign}}}\{R_T\ge m_T/2\}\ge\frac{m_T^2}{16T}\ge\frac1{32}.$$
--   In particular $V_T\ge m_T\ge\sqrt{T/2}$, and for this adversary $\inf_A\mathbb E_{A,D_{\mathrm{sign}}}R_T=m_T$.
--
--   This is the $\sqrt T$ half of both lower bounds; it holds for unrestricted continuum learners.
--
--   Differences from the source:
--   - encoding: the online protocol of Eq. (A.11) with standard Borel private states and the Borel σ-field of the weak topology on P(B²₂) → `Learner`/`Adversary`/`law` of the Protocol definition: Giry σ-field on `ProbabilityMeasure Disk`, rounds indexed from 0, one kernel per `t : ℕ` (those with t ≥ T unused), private states standard Borel types; reason: the Giry and weak-topology Borel σ-fields coincide on the Polish space B²₂; the other changes are index conventions; same learners, adversaries and laws
--   - encoding: E[·] and P{·} under the canonical law → Bochner integrals and measures of events under `law`/`sharpLaw` (`ENNReal.ofReal p ≤ μ {…}` for P{…} ≥ p); reason: the integrands are bounded Borel functions (Proposition A.1); same values
--   - encoding: D_sign: fresh independent uniform signs, g_t = ε_t e₁ → `Dsign`: trivial private state, preparation kernel constant (δ_{e₁} + δ_{−e₁})/2; reason: a fresh draw at every preparation step gives the product law on sign sequences
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 46, Theorem D.7

import Mathlib
import Definitions.Def_SwapDisk_Main_Protocol

namespace SwapDisk.Main

/-- Theorem D.7 (Statistical obstruction), p. 46: every admissible learner has
`E_{A,D_sign} R_T ≥ m_T` and `P_{A,D_sign}{R_T ≥ m_T/2} ≥ m_T²/(16T) ≥ 1/32`; hence
`V_T ≥ m_T ≥ √(T/2)`; and `inf_A E_{A,D_sign} R_T = m_T`. -/
theorem theorem_D_7 (T : ℕ) (hT : 2 ≤ T) :
    (∀ L : Learner, mT T ≤ expectedRegret T L Dsign ∧
      ENNReal.ofReal (mT T ^ 2 / (16 * T)) ≤
        law L Dsign T {z | mT T / 2 ≤ (Traj.hist z).regret}) ∧
    1 / 32 ≤ mT T ^ 2 / (16 * T) ∧
    mT T ≤ V T ∧ Real.sqrt ((T : ℝ) / 2) ≤ mT T ∧
    (⨅ L : Learner, expectedRegret T L Dsign) = mT T := by sorry

end SwapDisk.Main
