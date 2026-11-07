-- Prove2me | Theorems.Thm_RobustKellyTV_lemma_2_1
-- name    : RobustKellyTV.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:08.310126+00:00
-- url     : https://prove2.me/theorems/7fcd096e-e007-4d0f-89d3-c55d459e09a2
-- title:
--   Lemma 2.1 — existence and uniqueness of the oracle thresholds $a(U)\in(0,1)$, $b(U)\in(1,\infty)$
-- statement:
--   Assume the standing assumptions ($d\ge2$, $P_i>0$, $0<\epsilon_0<1-\min_iP_i$). Let $U\in\Delta_d^\circ\setminus\mathcal P_0$. Then the equation
--
--   $$\sum_{i=1}^d(zP_i-U_i)_+=z\epsilon_0$$
--
--   has exactly one solution $z>0$, and it lies in $(0,1)$; the equation
--
--   $$\sum_{i=1}^d(U_i-zP_i)_+=z\epsilon_0$$
--
--   has exactly one solution $z>0$, and it lies in $(1,\infty)$. The thresholds $a(U)$ and $b(U)$ are these solutions.
--
--   The thresholds determine the clipped-Kelly oracle $E_U$, so this lemma makes the oracle well defined.
--
--   Differences from the source:
--   - generalization: (10)–(11) have unique solutions a(U) ∈ (0,1) and b(U) ∈ (1,∞) → each equation has exactly one positive root, and that root lies in (0,1), resp. (1,∞); reason: z = 0 always solves (10), so uniqueness is stated among positive roots (proof p.21); this implies uniqueness inside the intervals
--   - encoding: a(U), b(U) defined through (10)–(11) → lowerThr/upperThr chosen among the positive roots, with a conjunct that they are roots; reason: ties the definition to the lemma
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.1, Lemma 2.1, p.7 (proof p.21)

import Mathlib
import Definitions.Def_RobustKellyTV_oracleE

namespace RobustKellyTV

/-- **Lemma 2.1** (Existence and uniqueness of the oracle thresholds). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Lemma 2.1, p.7.

If `U ∈ ∆°_d \ P0`, then (10)–(11) have unique solutions `a(U) ∈ (0, 1)` and `b(U) ∈ (1, ∞)`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. `z = 0` always solves (10), so uniqueness is stated among the
**positive** roots: (10) has exactly one positive root, and every positive root lies in `(0, 1)`;
(11) has exactly one positive root, and it lies in `(1, ∞)`. This is stronger than uniqueness inside
the intervals (it follows from the proof, p.21). The last conjunct of each half says that the
defined thresholds `lowerThr σ U`, `upperThr σ U` are these roots. -/
theorem lemma_2_1 {d : ℕ} (σ : Setting d) (U : Fin d → ℝ) (hU : U ∈ interiorSimplex d)
    (hU0 : U ∉ nullBall σ) :
    ((∃! z, IsLowerRoot σ U z) ∧ (∀ z, IsLowerRoot σ U z → z < 1) ∧
        IsLowerRoot σ U (lowerThr σ U)) ∧
      ((∃! z, IsUpperRoot σ U z) ∧ (∀ z, IsUpperRoot σ U z → 1 < z) ∧
        IsUpperRoot σ U (upperThr σ U)) := by sorry

end RobustKellyTV
