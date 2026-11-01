-- Prove2me | Theorems.Thm_SmallLossGraph_proof_thm_3_4_unbiased
-- name    : SmallLossGraph.proof_thm_3_4_unbiased
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:35.909269+00:00
-- url     : https://prove2.me/theorems/fa7d8ee1-e889-42c0-a1d6-bb05387d8b1c
-- title:
--   Proof of Theorem 3.4 — the estimator is unbiased on non-frozen arms
-- statement:
--   Let $G$ be a graph on the arms whose independent sets have at most $\alpha$ vertices, $p$ a probability vector, $\ell\in[0,1]^d$ and $\varepsilon'>0$. Let $F$, $w$ and $\tilde\ell$ be the frozen set, the sampling distribution and the estimated losses of one round of Algorithm 1 with $\gamma=\varepsilon'/(4\alpha)$, $\gamma'=\gamma/3$, where $\tilde\ell$ depends on the drawn arm $I\sim w$. For every non-frozen arm $i\notin F$,
--
--   $$
--   \mathbb E_{I\sim w}\big[\tilde\ell_i\big]=\sum_{j}w_j\,\tilde\ell_i(I=j)=\ell_i .
--   $$
--
--   Unbiasedness on the non-frozen arms is what lets the loss of the algorithm be compared with the estimated loss seen by the full-information algorithm.
--
--   Differences from the source:
--   - reading: the display Σ_{j∈N^t_i} w^t_j ℓ̃^t_j = ℓ^t_i → Σ_j w_j ℓ̃_i(I = j) = ℓ_i, the expectation of ℓ̃_i over the drawn arm; reason: the printed display is garbled (it sums estimates of other arms); the sentence states unbiasedness, i.e. E[ℓ̃_i] = ℓ_i
--   - encoding: α an upper bound on the size of maximum independent sets (Algorithm 1) → IndepBound G α: every independent set of G has at most α vertices; reason: the same condition α(G) ≤ α, stated without Mathlib's indepNum supremum
--   - encoding: Algorithm 1, line 5, divides by 1 − Σ_{j∈F} p_j, undefined when every arm carrying probability is frozen → in that case w = p (sampling convention); reason: the case cannot occur for ε′ < 1 (Lemma 3.1), so no instance of the paper changes; the convention keeps w a probability vector
--   - encoding: round t of Algorithm 1 (p^t, G^t, ℓ^t) → one round with the superscript t dropped; reason: the statement concerns a single round
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, proof of Theorem 3.4, second property, p.11

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

namespace SmallLossGraph

/-- **Proof of Theorem 3.4: the estimator is unbiased on non-frozen arms.**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, proof of Theorem 3.4, p.11: "Second, although the
estimator is no longer unbiased for all arms, it is unbiased for all non-frozen arms `i ∉ F^t` at
all rounds `t`, i.e., `∑_{j∈N^t_i} w^t_j ℓ̃^t_j = ℓ^t_i`."

Let `α` bound the independent sets of `G`, `p` be a probability vector, `ℓ ∈ [0,1]^d`, `ε′ > 0`,
and `w`, `F`, `ℓ̃` those of one round of Algorithm 1 with `γ = ε′/(4α)`, `γ′ = γ/3`. For every
non-frozen arm `i ∉ F`, the expectation of `ℓ̃_i` over the drawn arm `I ∼ w` is `ℓ_i`:
`∑_j w_j ℓ̃_i(I = j) = ℓ_i`.

**Formalization Note** The printed display is read as the expectation `E_{I∼w}[ℓ̃_i] = ℓ_i`
(the display's sum over `j ∈ N_i` of `w_j` times the estimate of `i` when `j` is drawn). -/
theorem proof_thm_3_4_unbiased {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ) (hα : IndepBound G α)
    (p : Fin d → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (ℓ : Fin d → ℝ) (hℓ : ∀ i, ℓ i ∈ Set.Icc (0 : ℝ) 1) (ε' : ℝ) (hε' : 0 < ε') (i : Fin d)
    (hi : i ∉ frozen G p (gamma ε' α) (gammaPrime ε' α)) :
    ∑ j, sampling G p (gamma ε' α) (gammaPrime ε' α) j *
        estLoss G ℓ p (gamma ε' α) (gammaPrime ε' α) j i = ℓ i := by sorry

end SmallLossGraph
