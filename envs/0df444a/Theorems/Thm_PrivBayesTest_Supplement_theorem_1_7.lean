-- Prove2me | Theorems.Thm_PrivBayesTest_Supplement_theorem_1_7
-- name    : PrivBayesTest.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:11:54.908504+00:00
-- url     : https://prove2.me/theorems/45f6c307-08f0-4a55-94c2-98ba43240bbf
-- title:
--   Theorem 1.7: no $\varepsilon$-edge-DP algorithm recovers the SBM communities exactly when $d_\varepsilon(i\to j)<1$ (corrected: $p_i,p_j>0$)
-- statement:
--   Let $(\sigma,G)\sim\mathrm{SBM}(n,p,\log(n)Q/n)$ with communities $[k]$, where $p$ is a probability vector on $[k]$ and $Q\in\mathbb R_+^{k\times k}$ is symmetric, and let $\varepsilon>0$. Suppose there are communities $i\ne j$ with $p_i>0$, $p_j>0$ and
--
--   $$d_\varepsilon(i\to j)<1.$$
--
--   Then for every sequence $(\mathcal A_n)_{n\ge1}$ of algorithms, where $\mathcal A_n$ maps a graph on $[n]$ to a random labelling $\tilde\sigma\in[k]^n$ and is $\varepsilon$-edge differentially private, the probability that there is a permutation $\pi$ of $[k]$ with $\tilde\sigma_v=\pi(\sigma_v)$ for all $v$ tends to $0$ as $n\to\infty$.
--
--   Since $d_\varepsilon(i\to j)\ge c_\varepsilon(i,j)$, this lower bound is weaker than the one Conjecture 1.6 predicts; Theorem 4.8 shows that the gap is real.
--
--   Differences from the source:
--   - correction: a pair i ≠ j with d_ε(i→j) < 1 → additionally p_i > 0 and p_j > 0; reason: the printed statement is false for a pair of empty communities: k = 2, p = (1, 0), Q with all entries 1 gives θ_1 = θ_2 = (1, 0), so d_ε(1→2) = 0 < 1, yet σ ≡ 1 almost surely and the constant labelling (ε-edge DP for every ε) recovers σ with probability 1; the proof uses p_i m(1+o(1)) and p_j m(1+o(1)) vertices of the two communities (p.17)
--   - encoding: for every ε-edge DP algorithm the success probability is o(1) → for every sequence (A_n) of ε-edge-DP maps from graphs on [n] to laws on [k]^n, the success probability tends to 0; reason: an algorithm for all n is such a sequence, and finite output sets make every randomized algorithm a probability mass function
--   - encoding: edge probability log(n)Q_ab/n → min(1, log(n)Q_ab/n); reason: the two differ only for finitely many n, which do not affect the limit
--   - encoding: I_θ, d_ε with the convention I_0(x) = +∞ for x > 0 → values in ℝ≥0∞; reason: same values
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Theorem 1.7, p.8; proof §4.1, pp.16-17

import Mathlib
import Definitions.Def_PrivBayesTest_Supplement_sbmWeight
import Definitions.Def_PrivBayesTest_Supplement_exactRecoveryProb
import Definitions.Def_PrivBayesTest_Supplement_dEps

open Filter Topology

namespace PrivBayesTest

namespace Supplement

/-- **Theorem 1.7 (Lower bound on private exact recovery)** (Jacobsen, *Optimal Error Exponents
for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256
abff2fdd…124ef), Theorem 1.7, p.8, PDF p.8; proof §4.1, pp.16–17).
Let `(σ, G) ∼ SBM(n, p, log(n) Q / n)` with communities `[k]`, `Q ∈ ℝ₊^{k×k}` symmetric. If
`d_ε(i → j) < 1` for some `i ≠ j` (with `p_i, p_j > 0`), then for every sequence of ε-edge-DP
algorithms `A_n` labelling the vertices of `G`, the probability that `A_n(G)` equals `σ` up to a
permutation of `[k]` tends to `0`.

**Formalization Note**
* `p_i > 0` and `p_j > 0` are added (minimal correction): with `p_i = 0` the statement is false
  (`k = 2`, `p = (1, 0)`, `Q` constant: `θ₁ = θ₂`, so `d_ε(1 → 2) = 0`, yet the constant
  labelling is 0-DP and recovers `σ` with probability 1). The proof uses `p_i m (1 + o(1))` and
  `p_j m (1 + o(1))` vertices of the two communities (p.17).
* "For every ε-edge DP algorithm … the probability is `o(1)`" is stated for every sequence
  `(A_n)_n` of algorithms, `A_n` on `n` vertices and ε-edge DP; the limit is unchanged if
  finitely many `A_n` are altered.
* `p` is a probability vector and `Q` is entrywise nonnegative and symmetric, as in Definition 1.5
  (p.6) and §4.1 (p.16); edge probabilities `log(n) Q_{ab}/n` are truncated at `1` for the
  finitely many small `n` where they exceed it (`logRegime`). -/
theorem theorem_1_7 {k : ℕ} (p : Fin k → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : ∑ ℓ, p ℓ = 1)
    (Q : Matrix (Fin k) (Fin k) ℝ) (hQsymm : Q.IsSymm) (hQ0 : ∀ a b, 0 ≤ Q a b)
    (ε : ℝ) (hε : 0 < ε) (i j : Fin k) (hij : i ≠ j) (hpi : 0 < p i) (hpj : 0 < p j)
    (hd : dEps p Q ε i j < 1)
    (A : ∀ n : ℕ, SimpleGraph (Fin n) → PMF (Fin n → Fin k)) (hA : ∀ n, IsEdgeDP ε (A n)) :
    Tendsto (fun n => exactRecoveryProb p (logRegime Q n) (A n)) atTop (𝓝 0) := by sorry

end Supplement

end PrivBayesTest
