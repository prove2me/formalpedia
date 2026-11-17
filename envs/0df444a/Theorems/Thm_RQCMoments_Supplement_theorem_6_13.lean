-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_6_13
-- name    : RQCMoments.Supplement.theorem_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:54:02.992577+00:00
-- url     : https://prove2.me/theorems/75df855e-a4e5-4e8d-a33f-092eb720c4bc
-- title:
--   Theorem 6.13 — $d_{TV}(X_kY,XY)=O(\varepsilon\log(2/\varepsilon))+2^{-\Omega(k)}$
-- statement:
--   Under the assumptions of Theorem 6.11 (in particular $\varepsilon\in[0,1]$),
--
--   $$d_{TV}(X_kY,XY)=O\big(\varepsilon\log(2/\varepsilon)\big)+2^{-\Omega(k)},$$
--
--   where at $\varepsilon=0$ the first term is interpreted as zero. Here $d_{TV}(P,Q)=\sup_A|P(A)-Q(A)|$ over measurable sets $A$.
--
--   Total variation is stronger than Kolmogorov distance; this upgrades Theorem 6.11 at the cost of a logarithmic factor in $\varepsilon$.
--
--   **Formalization Note** The assumptions of Theorem 6.11 are repeated, including the conjunct identifying the Haar block law $\mathrm{Beta}(a,N-a)$. The bound is $C\varepsilon\log_2(2/\varepsilon)+C2^{-ck}$ with absolute $C,c>0$ chosen first (logarithms are base two, p.13). At $\varepsilon=0$ the Lean term $C\cdot0\cdot\log_2(2/0)$ is $0$, the paper's convention. $d_{TV}$ is the published `totalVariationDistance`.
--
--   Differences from the source:
--
--   - encoding: O(ε log(2/ε)) + 2^{−Ω(k)}, first term 0 at ε = 0 → C·ε·log₂(2/ε) + C·2^{−c·k} with absolute C, c > 0 chosen first (0 at ε = 0 in Lean); reason: asymptotic notation with absolute constants chosen first; same content
--   - reading: "X ∼ Beta(a, N−a) its Haar counterpart" (assumption of Theorem 6.11) → conjunct: the Haar law of the block probability is betaMeasure a (N − a); reason: as in Theorem 6.11
--   - encoding: law of X_k Y, XY with Y independent → pushforward of the product measure under multiplication (productLaw); reason: same law
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.13, (224), p.49 (PDF p.51); Theorem 6.11, p.45

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_Supplement_blockProb
import Definitions.Def_ProbabilityTheory_chapter_08_def_8_5_F000

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 6.13** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.13, (224), p.49, PDF p.51).
Under the assumptions of Theorem 6.11 (in particular `ε ∈ [0,1]`),
`d_TV(X_k Y, X Y) = O(ε log(2/ε)) + 2^{−Ω(k)}` (224), where at `ε = 0` the first term is interpreted as
zero.

**Formalization Note** The assumptions of Theorem 6.11: `k ≥ 1`, integers `a ≥ 2πk`, `N > 2a`,
`ε ∈ [0,1]`, a block `S` of `a` basis states, a column `y`, `U ∼ μ` an `ε`-approximate `k`-design on
`U(N)` (`IsStrongDesign μ k k ε`), `X_k` the block probability, `X ∼ Beta(a, N−a)` its Haar counterpart
(the first conjunct) and `Y ∼ Beta(1, a−1)` independent. `O(ε log(2/ε)) + 2^{−Ω(k)}` is
`C·ε·log₂(2/ε) + C·2^{−ck}` with absolute `C, c > 0` chosen first; logarithms are base two (p.13). At
`ε = 0` the term `C·0·log₂(2/0)` is `0` in Lean, which is the paper's interpretation. `d_TV` (3) is the
published `totalVariationDistance` (supremum over measurable sets of `|P(A) − Q(A)|`). -/
theorem theorem_6_13 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ a N : ℕ, 2 * Real.pi * k ≤ (a : ℝ) → 2 * a < N →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ S : Finset (Fin N), S.card = a → ∀ y : Fin N,
        (QAlgorithms.Schur.unitaryHaar N).map (blockProb S y) =
            ProbabilityTheory.betaMeasure a ((N : ℝ) - a) ∧
        ∀ μ : Measure (Matrix.unitaryGroup (Fin N) ℂ), IsStrongDesign μ k k ε →
          totalVariationDistance
              (productLaw (μ.map (blockProb S y)) (ProbabilityTheory.betaMeasure 1 ((a : ℝ) - 1)))
              (productLaw (ProbabilityTheory.betaMeasure a ((N : ℝ) - a))
                (ProbabilityTheory.betaMeasure 1 ((a : ℝ) - 1))) ≤
            C * ε * Real.logb 2 (2 / ε) + C * (2 : ℝ) ^ (-(c * k)) := by sorry

end Supplement

end RQCMoments
