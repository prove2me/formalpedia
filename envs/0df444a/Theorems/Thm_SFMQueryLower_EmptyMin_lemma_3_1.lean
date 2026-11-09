-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_lemma_3_1
-- name    : SFMQueryLower.EmptyMin.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:04.39191+00:00
-- url     : https://prove2.me/theorems/f04de1ac-5359-45aa-9ea6-16163cadd801
-- title:
--   Lemma 3.1 — full exponential passing bound at the one-quarter budget
-- statement:
--   There are an absolute $a>0$ and threshold $K\ge2$ such that the following holds for every integer $k\ge K$, every finite ground set $V$ with $m=|V|\ge k^2$, and every deterministic causal algorithm $B$. Sample an ordered pair of disjoint $k$-subsets $P,R\subseteq V$ uniformly. Give $B$ only $k,V$ and access to the case-number oracle $O_{P,R}$. Then
--   $$\Pr_{P,R}\{B\text{ receives reply }2\text{ within }\lfloor k\log k/4\rfloor\text{ queries}\}\le 2^{-a\sqrt{k}}.$$
--   Here $\log$ is the natural logarithm. Both constants are uniform over $V$ and $B$. The full exponentially decreasing probability bound is retained, rather than only its constant-probability consequence.
--
--   **Formalization Note** Replies are `Fin 3` case numbers, not hard-function values. Early stopping or internal divergence cannot create a passing reply. No explicit numeric witness to the asymptotic constant is chosen.
--
--   Differences from the source:
--   - encoding: finite labeled ground sets and their subsets → Fin n and Finset (Fin n); reason: bijections relabel every finite source instance
--   - encoding: 1 / 2^{Omega(sqrt k)} for sufficiently large k → there exist a>0,K>=2 before every k,m,B, with bound 2^(-a sqrt k); reason: the uniform quantified meaning of the source asymptotic notation; the exact natural-log floor budget is unchanged
--   - encoding: uniform disjoint k-subsets of V and ternary oracle replies → normalized sum on the full finite LayerPair type and replies in Fin 3; reason: every ordered pair is represented once; m>=k^2 and k>=2 ensure the sample space is nonempty
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma 3.1, printed p. 9 / PDF p. 10; proof Appendix B.1, printed pp. 16–17 / PDF pp. 17–18

import Definitions.Def_SFMQueryLower_EmptyMin_LayerSampling

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Fox, Lemma 3.1, printed p.9 / PDF p.10; proof Appendix B.1, pp.16–17.
The exponent constant and size threshold precede all dimensions and strategies.
The budget is exactly `⌊k log k / 4⌋`, retaining the full exponential conclusion. -/
theorem lemma_3_1 :
    ∃ a : ℝ, 0 < a ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ k : ℕ, K ≤ k → ∀ m : ℕ, k ^ 2 ≤ m →
      ∀ B : OracleStrategy (Finset (Fin m)) (Fin 3) Bool,
        passingProbability (k := k) B ≤
          ENNReal.ofReal ((2 : ℝ) ^ (-a * Real.sqrt (k : ℝ))) := by sorry

end SFMQueryLower.EmptyMin
