-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_euclidean_coreset_lower_bound
-- name    : TightCoreset2027.Euclidean.euclidean_coreset_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:06:37.506311+00:00
-- url     : https://prove2.me/theorems/7c2bdc79-919d-4e91-aab3-a5012c072e5d
-- title:
--   Theorem 1.2 — Euclidean coreset lower bound at every error scale
-- statement:
--   Fix any real exponent $z\ge1$. There are a positive constant $c_z$ and nonnegative integer degrees $a_z,b_z$, depending only on $z$, such that for every integer $k\ge1$ and every $0<\varepsilon<1$, some positive finite dimension $d$ and finite set $X\subseteq\mathbb R^d$ force every strong $\varepsilon$-coreset $(S,w)$ for $(k,z)$-clustering to satisfy
--
--   $$|S|\ge\frac{c_z\min\{k^{(2z+2)/(z+2)}\varepsilon^{-2},\ k\varepsilon^{-z-2}\}}{[\log(2+k)]^{a_z}[\log(2+1/\varepsilon)]^{b_z}}.$$
--
--   The coreset must preserve every set of exactly $k$ distinct ambient centers, with absolute relative error, and may use any nonnegative weights on any subset of $X$. No sampling or mass constraint is imposed. The dimension and dataset may depend on $z,k,\varepsilon$ but precede the candidate subset and its weights. This is the full lower bound in Theorem 1.2 under footnote 1's asymptotic convention, including all real exponents, both error regimes, $k=1$, and arbitrarily small positive errors.
--
--   **Formalization Note** The constants and log degrees are quantified before $k,\varepsilon$. All logarithm arguments exceed $2$ in this domain. The calibrated general-power construction and boundary arguments of §2.5 remain proof obligations; they are not hypotheses of this theorem.
--
--   Differences from the source:
--   - encoding: tilde-Omega with z-only constants and finite polylogarithmic factors by footnote 1 → positive c_z and natural degrees a_z,b_z chosen before k and epsilon, with the displayed denominator; reason: this is precisely the source asymptotic convention, not instance-dependent constants
--   - encoding: a finite subset of Euclidean space and every exact-k ambient center set → Finset (EuclideanSpace R (Fin d)) for data and all ambient queries; reason: finite sets preserve distinct support and exact cardinality; Euclidean coordinates use an isometric representation
--   - encoding: arbitrary nonnegative weights defined on S → an arbitrary ambient NNReal function whose values outside S are ignored; reason: every source weight function extends by zero, including zero weights and the empty candidate
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Theorem 1.2, printed p. 3 / PDF p. 5; footnote 1 and Definition 1.1, printed p. 1 / PDF p. 3; §2.5, printed pp. 19–21 / PDF pp. 21–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_coresetModel
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

theorem euclidean_coreset_lower_bound (z : ℝ) (hz : 1 ≤ z) :
    ∃ c : ℝ, 0 < c ∧ ∃ a b : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
          ∀ (S : Finset (Point d)) (w : Point d → NNReal),
            IsStrongCoreset z ε k X S w →
              c * lowerBoundScale z k ε /
                ((Real.log (2 + (k : ℝ))) ^ a * (Real.log (2 + 1 / ε)) ^ b)
                ≤ (S.card : ℝ) := by sorry

end TightCoreset2027.Euclidean
