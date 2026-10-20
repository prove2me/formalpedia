-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_entropyMinimax
-- name    : QAlgorithms.Papers.Independent.Information100.P69.entropyMinimax
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:11:58.841524+00:00
-- url     : https://prove2.me/theorems/cbe96a05-81b7-4d01-b25b-42d95913455f
-- title:
--   Entropy minimax and symmetric maximizer
-- statement:
--   Assume F1–F3 and fix $n\ge1$. For a physical input marginal $\rho$, let $|\chi_\rho\rangle=(I\otimes\sqrt\rho)|\Gamma\rangle$, and let $f(\rho,M)$ be the relative entropy of the target and alternative outputs on this purification. The function $f$ is concave in $\rho$ and convex in the CPTP alternative $M$, allowing $+\infty$. Moreover
--   $$E_n=\max_{\rho\in\mathcal D(A^n)}\inf_{M\in\mathcal F_n}f(\rho,M).$$
--   The maximum is attained. For any fixed permutation-covariant alternative $M$ with $M\ge_{\rm CP}\eta R_\omega^{\otimes n}$ for some $\eta>0$, a permutation-invariant $\rho$ attains $D_{\rm ch}(\mathcal N^{\otimes n}\|M)$. No F4 assumption on the whole family is needed for this last assertion. The purification has reference marginal $\rho^T$.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 38, Lemma 32

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 32, concavity, convexity, entropy minimax with attainment, and a symmetric
maximizer for a fixed covariant alternative, PDF pp.38–39. -/
theorem entropyMinimax [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) (n : ℕ) (hn : 1 ≤ n) :
    (∀ rho sigma : Matrix (Sites A n) (Sites A n) ℂ, IsDensityMatrix rho → IsDensityMatrix sigma →
      ∀ M : Superop (Sites A n) (Sites B n), IsChannel M → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ENNReal.ofReal u*entropyFunction (power N n) M rho +
          ENNReal.ofReal (1-u)*entropyFunction (power N n) M sigma ≤
          entropyFunction (power N n) M ((u:ℂ) • rho+(1-u:ℂ) • sigma)) ∧
    (∀ rho : Matrix (Sites A n) (Sites A n) ℂ, IsDensityMatrix rho →
      ∀ M L : Superop (Sites A n) (Sites B n), IsChannel M → IsChannel L →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        entropyFunction (power N n) ((u:ℂ) • M+(1-u:ℂ) • L) rho ≤
          ENNReal.ofReal u*entropyFunction (power N n) M rho+
          ENNReal.ofReal (1-u)*entropyFunction (power N n) L rho) ∧
    (∃ rho : Matrix (Sites A n) (Sites A n) ℂ, IsDensityMatrix rho ∧
      resourceEntropy (power N n) (F n) = (⨅ M : F n, entropyFunction (power N n) M.val rho) ∧
      ∀ sigma : Matrix (Sites A n) (Sites A n) ℂ, IsDensityMatrix sigma →
        (⨅ M : F n, entropyFunction (power N n) M.val sigma) ≤ resourceEntropy (power N n) (F n)) ∧
    (∀ M : Superop (Sites A n) (Sites B n), IsChannel M →
      (∀ pi X, M (permute pi X) = permute pi (M X)) →
      (∃ eta : ℝ, 0 < eta ∧ CPLe ((eta:ℂ) • power (replacer omega) n) M) →
      ∃ rho : Matrix (Sites A n) (Sites A n) ℂ, IsDensityMatrix rho ∧
        (∀ pi, permute pi rho = rho) ∧ entropyFunction (power N n) M rho = channelEntropy (power N n) M) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
