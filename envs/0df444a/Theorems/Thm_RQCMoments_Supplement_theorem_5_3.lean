-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_5_3
-- name    : RQCMoments.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:49:43.821922+00:00
-- url     : https://prove2.me/theorems/5d9187cf-76f5-4fb8-a143-249c91198edd
-- title:
--   Theorem 5.3 — a $2k$-moment-matching distribution on $[0,1]$ induces an exact unitary $k$-design
-- statement:
--   Let $D>1$ be an integer and let $p$ be a distribution on $[0,1]$ whose moments of order up to $2k$ agree with those of $\mathrm{Beta}(1,D-1)$, i.e.
--
--   $$\mathbb E_{X\sim p}[f(X)]=\mathbb E_{X\sim\mathrm{Beta}(1,D-1)}[f(X)]\qquad\text{for every polynomial }f\text{ of degree at most }2k .$$
--
--   Then the unitary distribution $\mu(p)$ on $U(D)$ induced by $p$ (Definition 5.1) is an exact unitary $k$-design.
--
--   Applied to a discrete $p$ (a Gauss quadrature rule), this gives exact designs whose top-left entry has a discrete law, the starting point of the lower bound of Theorem 5.8.
--
--   **Formalization Note** $D>1$ is the standing assumption of Definition 5.1. "Distribution on $[0,1]$" is a probability measure on $\mathbb R$ giving $[0,1]^{\mathrm c}$ mass zero. Real polynomials are used in the moment condition. $\mathrm{Beta}(1,D-1)$ is the published `RQCMoments.porterThomas D`. An exact unitary $k$-design is `IsStrongDesign μ k k 0` (Remark 2.3).
--
--   Differences from the source:
--
--   - encoding: polynomials f of degree at most 2k in (112) → real polynomials of natDegree ≤ 2k; reason: complex polynomials follow by linearity; same condition
--   - encoding: exact unitary k-design → IsStrongDesign μ(p) k k 0; reason: Remark 2.3 (ε = 0)
--   - encoding: distribution p on [0,1] → probability measure p on ℝ with p([0,1]ᶜ) = 0; reason: same distributions; the induced measure only uses p on [0,1]
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.3, (112), p.32 (PDF p.34); Definition 5.1, p.31

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_porterThomas
import Definitions.Def_RQCMoments_Supplement_inducedMeasure

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 5.3** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.3, (112), p.32, PDF p.34).
For every distribution `p` on `[0,1]` whose moments of order up to `2k` agree with those of
`Beta(1, D − 1)`, i.e. `E_{X∼p}[f(X)] = E_{X∼Beta(1,D−1)}[f(X)]` for every polynomial `f` of degree
at most `2k` (112), the unitary distribution `μ(p)` on `U(D)` induced by `p` (Definition 5.1) is an
exact unitary `k`-design.

**Formalization Note** `D > 1` is the standing assumption of Definition 5.1. "Distribution on
`[0,1]`" is a probability measure on `ℝ` giving `[0,1]ᶜ` mass `0`. Real polynomials suffice in (112)
(complex ones follow by linearity); polynomials are `p`-integrable since `p` lives on `[0,1]`.
`Beta(1, D−1)` is the published `porterThomas D`. By Remark 2.3 an exact unitary `k`-design is
`IsStrongDesign μ k k 0`. `k` is any natural number. -/
theorem theorem_5_3 (D : ℕ) (hD : 1 < D) (k : ℕ) (p : Measure ℝ) [IsProbabilityMeasure p]
    (hp : p (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * k →
      ∫ x, f.eval x ∂p = ∫ x, f.eval x ∂(porterThomas D)) :
    IsStrongDesign (inducedMeasure D p) k k 0 := by sorry

end Supplement

end RQCMoments
