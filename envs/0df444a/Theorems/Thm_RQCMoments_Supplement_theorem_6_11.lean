-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_6_11
-- name    : RQCMoments.Supplement.theorem_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:53:19.241849+00:00
-- url     : https://prove2.me/theorems/0959d2e1-86bf-427e-823e-34be97356177
-- title:
--   Theorem 6.11 — $d_K(X_kY,XY)=2^{-\Omega(k)}+O(\varepsilon)$ for block probabilities of a design
-- statement:
--   Let $k\ge1$, let $a\ge2\pi k$ and $N>2a$ be integers, and let $\varepsilon\in[0,1]$. Let $X_k=\sum_{r\in S}|\langle r|U|y\rangle|^2$ be the probability of a fixed block $S$ of $a$ basis states in a fixed column $y$ for $U$ drawn from an $\varepsilon$-approximate $k$-design on $U(N)$, let $X\sim\mathrm{Beta}(a,N-a)$ be its Haar counterpart, and let $Y\sim\mathrm{Beta}(1,a-1)$ be independent of $X_k$ and $X$. Then
--
--   $$d_K(X_kY,XY)=\sup_{x\in\mathbb R}\big|F_{X_kY}(x)-F_{XY}(x)\big|=2^{-\Omega(k)}+O(\varepsilon).$$
--
--   With local invariance (Lemma 6.2), $X_kY$ is the law of a single output probability of the design, so this gives Kolmogorov convergence to Porter–Thomas at a rate exponential in $k$.
--
--   **Formalization Note** $2^{-\Omega(k)}+O(\varepsilon)$ is $C2^{-ck}+C\varepsilon$ with absolute $C,c>0$ chosen before all other data. "Its Haar counterpart" is a conjunct: under Haar the block probability has law $\mathrm{Beta}(a,N-a)$. The law of a product of independent variables is the image of the product measure under multiplication. The design is `IsStrongDesign μ k k ε`.
--
--   Differences from the source:
--
--   - encoding: 2^{−Ω(k)} + O(ε) → C·2^{−c·k} + C·ε with absolute C, c > 0 chosen first; reason: asymptotic notation with absolute constants chosen first; same content
--   - reading: "let X ∼ Beta(a, N−a) be its Haar counterpart" → conjunct: the Haar law of the block probability is betaMeasure a (N − a); reason: the sentence asserts the Haar law (Lemma 6.2); it is stated, not assumed
--   - encoding: law of X_k Y, XY with Y independent → pushforward of the product measure under multiplication (productLaw); reason: same law
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.11, (184), p.45 (PDF p.47)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_Supplement_blockProb

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 6.11** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.11, (184), p.45, PDF p.47).
Let `k` be a positive integer, let `a ≥ 2πk` and `N > 2a` be integers, and let `ε ∈ [0,1]`. Let
`X_k = ∑_{r∈S} |⟨r|U|y⟩|²` be the probability of a fixed block `S` of `a` basis states in a fixed
column `y` for `U` sampled from an `ε`-approximate `k`-design on `U(N)`, let `X ∼ Beta(a, N−a)` be its
Haar counterpart, and let `Y ∼ Beta(1, a−1)` be independent of `X_k` and `X`. Then
`d_K(X_k Y, X Y) = sup_x |F_{X_k Y}(x) − F_{XY}(x)| = 2^{−Ω(k)} + O(ε)` (184).

**Formalization Note** `2^{−Ω(k)} + O(ε)` is `C·2^{−ck} + C·ε` with absolute constants `C, c > 0`
chosen before `k, a, N, ε`, the block, the column and the design. "Its Haar counterpart" is the first
conjunct: under Haar the block probability has law `Beta(a, N − a)` (Mathlib's `betaMeasure`). The law
of a product of independent variables is `productLaw` (pushforward of the product measure). The
supremum over `x` is a bound for every real `z`. A design is `IsStrongDesign μ k k ε` (Remark 2.3). -/
theorem theorem_6_11 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ a N : ℕ, 2 * Real.pi * k ≤ (a : ℝ) → 2 * a < N →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ S : Finset (Fin N), S.card = a → ∀ y : Fin N,
        (QAlgorithms.Schur.unitaryHaar N).map (blockProb S y) =
            ProbabilityTheory.betaMeasure a ((N : ℝ) - a) ∧
        ∀ μ : Measure (Matrix.unitaryGroup (Fin N) ℂ), IsStrongDesign μ k k ε →
          ∀ z : ℝ,
            |(productLaw (μ.map (blockProb S y)) (ProbabilityTheory.betaMeasure 1 ((a : ℝ) - 1))
                (Set.Iic z)).toReal -
              (productLaw (ProbabilityTheory.betaMeasure a ((N : ℝ) - a))
                (ProbabilityTheory.betaMeasure 1 ((a : ℝ) - 1)) (Set.Iic z)).toReal| ≤
              C * (2 : ℝ) ^ (-(c * k)) + C * ε := by sorry

end Supplement

end RQCMoments
