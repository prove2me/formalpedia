-- Prove2me | Theorems.Thm_PrivBayesTest_Supplement_theorem_4_8
-- name    : PrivBayesTest.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:12:29.889209+00:00
-- url     : https://prove2.me/theorems/a84a3b61-40fe-4b81-b4e9-10611f4646d4
-- title:
--   Theorem 4.8: a four-community SBM with $D_\varepsilon=1+\eta$ and $C_\varepsilon<1$ on which $\varepsilon$-edge-DP exact recovery succeeds
-- statement:
--   Consider the four-community instance $\mathrm{SBM}(n,p,\log(n)Q/n)$ with $p=(\tfrac14,\tfrac14,\tfrac14,\tfrac14)$ and
--
--   $$Q=4\begin{bmatrix}K&0&L&0\\0&2K&0&L\\L&0&0&0\\0&L&0&0\end{bmatrix}.$$
--
--   For every $\eta\in(0,1)$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ there are constants $K,L>0$ for which
--
--   1. $D_\varepsilon=1+\eta$;
--   2. $C_\varepsilon<1$;
--   3. there is a sequence $(\mathcal A_n)_{n\ge1}$ of $\varepsilon$-edge differentially private algorithms whose probability of recovering $\sigma$ exactly (up to a permutation of the four communities) tends to $1$ as $n\to\infty$.
--
--   Here $C_\varepsilon$ and $D_\varepsilon$ are the minima of $c_\varepsilon(i,j)$ and $d_\varepsilon(i\to j)$ over all ordered pairs of distinct communities. The theorem refutes Conjecture 1.6, which predicted that exact recovery under $\varepsilon$-edge DP is possible if and only if $C_\varepsilon\ge1$, and shows that the threshold $D_\varepsilon<1$ of Theorem 1.7 cannot be raised to $D_\varepsilon<1+\eta$.
--
--   Differences from the source:
--   - reading: there exist constants K, L → there exist K, L with K > 0 and L > 0; reason: the entries of the SBM matrix Q are nonnegative (p.16) and the proof's choices (K large, L = (1+η)/(1 − e^{−ε} + εy*(ε))) are positive; this is the stronger reading
--   - encoding: an ε-edge DP algorithm that succeeds with probability 1 − o(1) → a sequence (A_n) of maps from graphs on [n] to laws on [4]^n, each ε-edge DP, with success probability tending to 1; reason: the proof's algorithm is ε-DP for all sufficiently large n, and replacing finitely many A_n by a constant labelling (ε-edge DP) changes neither DP nor the limit
--   - encoding: edge probability log(n)Q_ab/n → min(1, log(n)Q_ab/n); reason: the two differ only for finitely many n, which do not affect the limit
--   - encoding: D_ε = 1 + η, C_ε < 1 with values of I_θ in [0, +∞] → equalities and inequalities in ℝ≥0∞, D_ε = ofReal(1 + η); reason: same values
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Theorem 4.8 (formal version of Theorem 1.8, p.8), p.20; proof pp.20-23

import Mathlib
import Definitions.Def_PrivBayesTest_Supplement_sbmWeight
import Definitions.Def_PrivBayesTest_Supplement_exactRecoveryProb
import Definitions.Def_PrivBayesTest_Supplement_dEps
import Definitions.Def_PrivBayesTest_Supplement_fourQ

open Filter Topology

namespace PrivBayesTest

namespace Supplement

/-- **Theorem 4.8** (formal version of Theorem 1.8; refutes Conjecture 1.6) (Jacobsen, *Optimal
Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256
abff2fdd…124ef), Theorem 4.8, p.20, PDF p.20; proof pp.20–23).
For every `η ∈ (0, 1)` there is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)` there are constants
`K, L` for which the four-community instance `SBM(n, (1/4,1/4,1/4,1/4), log(n) Q / n)`,
`Q = 4·[[K,0,L,0],[0,2K,0,L],[L,0,0,0],[0,L,0,0]]`, satisfies `D_ε = 1 + η` and `C_ε < 1`, and
some sequence of ε-edge-DP algorithms recovers `σ` exactly (up to a permutation of the four
communities) with probability tending to `1`.

**Formalization Note**
* `D_ε` and `C_ε` are the general minima over all ordered pairs of distinct communities
  (`DEps`, `CEps`), not the closed forms of the proof.
* The constants `K, L` are required to be positive (the entries of `Q` are nonnegative, p.16; the
  proof takes `K` large and `L = (1 + η)/(1 − e^{−ε} + ε y*(ε)) > 0`).
* "There is an ε-edge DP algorithm that succeeds with probability `1 − o(1)`" is a sequence
  `(A_n)_n`, each `A_n` ε-edge DP on `n` vertices, whose exact-recovery probability tends to `1`.
  Requiring DP for every `n` is equivalent to the proof's "for sufficiently large `n`" (replace the
  finitely many exceptional `A_n` by a constant labelling, which is 0-DP).
* Edge probabilities are truncated at `1` for the finitely many small `n` (`logRegime`). -/
theorem theorem_4_8 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
        DEps fourP (fourQ K L) ε = ENNReal.ofReal (1 + η) ∧
        CEps fourP (fourQ K L) ε < 1 ∧
        ∃ A : ∀ n : ℕ, SimpleGraph (Fin n) → PMF (Fin n → Fin 4),
          (∀ n, IsEdgeDP ε (A n)) ∧
          Tendsto (fun n => exactRecoveryProb fourP (logRegime (fourQ K L) n) (A n))
            atTop (𝓝 1) := by sorry

end Supplement

end PrivBayesTest
