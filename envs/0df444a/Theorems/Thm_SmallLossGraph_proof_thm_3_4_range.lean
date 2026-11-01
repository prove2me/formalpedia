-- Prove2me | Theorems.Thm_SmallLossGraph_proof_thm_3_4_range
-- name    : SmallLossGraph.proof_thm_3_4_range
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:48.992253+00:00
-- url     : https://prove2.me/theorems/e66b1df7-5d8e-4696-b987-69a35733b63e
-- title:
--   Proof of Theorem 3.4 — the estimated losses lie in $[0,1/\gamma']$
-- statement:
--   Let $G$ be a graph on the arms whose independent sets have at most $\alpha$ vertices, $p$ a probability vector, $\ell\in[0,1]^d$ a loss vector and $\varepsilon'>0$. In one round of Algorithm 1 with thresholds $\gamma=\varepsilon'/(4\alpha)$ and $\gamma'=\gamma/3$, for every drawn arm $I$ and every arm $i$ the estimated loss satisfies
--
--   $$
--   0\le\tilde\ell_i\le\frac1{\gamma'} .
--   $$
--
--   So the full-information algorithm is always fed losses in $[0,L]$ with $L=1/\gamma'=12\alpha/\varepsilon'$, the range its guarantee is invoked on.
--
--   Differences from the source:
--   - generalization: the maximum estimated loss is L = 1/γ′ → 0 ≤ ℓ̃_i ≤ 1/γ′; reason: the Lean statement adds the lower bound; dropping that conjunct gives the printed property
--   - encoding: α an upper bound on the size of maximum independent sets (Algorithm 1) → IndepBound G α: every independent set of G has at most α vertices; reason: the same condition α(G) ≤ α, stated without Mathlib's indepNum supremum
--   - encoding: Algorithm 1, line 5, divides by 1 − Σ_{j∈F} p_j, undefined when every arm carrying probability is frozen → in that case w = p (sampling convention); reason: the case cannot occur for ε′ < 1 (Lemma 3.1), so no instance of the paper changes; the convention keeps w a probability vector
--   - encoding: round t of Algorithm 1 (p^t, G^t, ℓ^t) → one round with the superscript t dropped; reason: the statement concerns a single round
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, proof of Theorem 3.4, first property, p.11

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

namespace SmallLossGraph

/-- **Proof of Theorem 3.4: the estimated losses lie in `[0, 1/γ′]`.**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, proof of Theorem 3.4, p.11: "First, freezing
guarantees that the maximum estimated loss is `L = 1/γ′` (since the probability of being
observed is at least `γ′` for any non-frozen arm; else this arm becomes frozen at step 4 of the
algorithm)."

Let `α` bound the independent sets of `G`, `p` be a probability vector, `ℓ ∈ [0,1]^d` and
`ε′ > 0`. In one round of Algorithm 1 with `γ = ε′/(4α)`, `γ′ = γ/3`, for every drawn arm `I`
and every arm `i`, `0 ≤ ℓ̃_i ≤ 1/γ′`.

**Formalization Note** One round; `ℓ̃` is the estimator of line 7 for the drawn arm `I`. The
lower bound `0 ≤ ℓ̃_i` is the other half of "the estimated losses lie in `[0, L]`", the range on
which `A` is run. -/
theorem proof_thm_3_4_range {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ) (hα : IndepBound G α)
    (p : Fin d → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (ℓ : Fin d → ℝ) (hℓ : ∀ i, ℓ i ∈ Set.Icc (0 : ℝ) 1) (ε' : ℝ) (hε' : 0 < ε') (I i : Fin d) :
    0 ≤ estLoss G ℓ p (gamma ε' α) (gammaPrime ε' α) I i ∧
      estLoss G ℓ p (gamma ε' α) (gammaPrime ε' α) I i ≤ 1 / gammaPrime ε' α := by sorry

end SmallLossGraph
