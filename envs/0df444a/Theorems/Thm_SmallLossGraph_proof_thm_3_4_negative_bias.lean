-- Prove2me | Theorems.Thm_SmallLossGraph_proof_thm_3_4_negative_bias
-- name    : SmallLossGraph.proof_thm_3_4_negative_bias
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:55:04.128705+00:00
-- url     : https://prove2.me/theorems/974027d6-eff4-4bcf-8889-bcf0a45d04c8
-- title:
--   Proof of Theorem 3.4 — the estimator is negatively biased on every arm
-- statement:
--   Let $G$ be a graph on the arms whose independent sets have at most $\alpha$ vertices, $p$ a probability vector, $\ell\in[0,1]^d$ and $\varepsilon'>0$. Let $w$ and $\tilde\ell$ be the sampling distribution and the estimated losses of one round of Algorithm 1 with $\gamma=\varepsilon'/(4\alpha)$, $\gamma'=\gamma/3$. For every arm $i$, frozen or not,
--
--   $$
--   \mathbb E_{I\sim w}\big[\tilde\ell_i\big]=\sum_{j}w_j\,\tilde\ell_i(I=j)\le\ell_i .
--   $$
--
--   This optimism is what allows the estimated loss of the comparator to be bounded by its true loss.
--
--   Differences from the source:
--   - encoding: α an upper bound on the size of maximum independent sets (Algorithm 1) → IndepBound G α: every independent set of G has at most α vertices; reason: the same condition α(G) ≤ α, stated without Mathlib's indepNum supremum
--   - encoding: Algorithm 1, line 5, divides by 1 − Σ_{j∈F} p_j, undefined when every arm carrying probability is frozen → in that case w = p (sampling convention); reason: the case cannot occur for ε′ < 1 (Lemma 3.1), so no instance of the paper changes; the convention keeps w a probability vector
--   - encoding: round t of Algorithm 1 (p^t, G^t, ℓ^t) → one round with the superscript t dropped; reason: the statement concerns a single round
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, proof of Theorem 3.4, third property, p.11

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

namespace SmallLossGraph

/-- **Proof of Theorem 3.4: the estimator is negatively biased on every arm.**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, proof of Theorem 3.4, p.11: "Third, it always
negatively (optimistically) biased regardless whether the arm is frozen or not, i.e.,
`E[ℓ̃^t_i] ≤ ℓ^t_i`."

Let `α` bound the independent sets of `G`, `p` be a probability vector, `ℓ ∈ [0,1]^d`, `ε′ > 0`,
and `w`, `ℓ̃` those of one round of Algorithm 1 with `γ = ε′/(4α)`, `γ′ = γ/3`. For every arm
`i`, the expectation of `ℓ̃_i` over the drawn arm `I ∼ w` is at most `ℓ_i`:
`∑_j w_j ℓ̃_i(I = j) ≤ ℓ_i`.

**Formalization Note** One round; the expectation is over the arm drawn in that round. -/
theorem proof_thm_3_4_negative_bias {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ)
    (hα : IndepBound G α) (p : Fin d → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (ℓ : Fin d → ℝ) (hℓ : ∀ i, ℓ i ∈ Set.Icc (0 : ℝ) 1) (ε' : ℝ) (hε' : 0 < ε') (i : Fin d) :
    ∑ j, sampling G p (gamma ε' α) (gammaPrime ε' α) j *
        estLoss G ℓ p (gamma ε' α) (gammaPrime ε' α) j i ≤ ℓ i := by sorry

end SmallLossGraph
