-- Prove2me | Theorems.Thm_UnderstandingML_sign_and_or
-- name    : UnderstandingML.sign_and_or
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:00:42.229253+00:00
-- url     : https://prove2.me/theorems/6f039530-d540-49ee-b8cf-7bee408562fe
-- title:
--   Lemma 20.4: on {±1}^k, ∧ᵢxᵢ = sign(1 − k + ∑ᵢxᵢ) and ∨ᵢxᵢ = sign(k − 1 + ∑ᵢxᵢ)
-- statement:
--   **Lemma 20.4.** Suppose that a neuron $v$, that implements the sign activation function, has $k$ incoming edges, connecting it to neurons whose outputs are in $\{\pm1\}$. Then, by adding one more edge, linking a "constant" neuron to $v$, and by adjusting the weights on the edges to $v$, the output of $v$ can implement the conjunction or the disjunction of its inputs.
--
--   Formally (the proof's formulas): for $x \in \{\pm1\}^k$, $1 - k + \sum_i x_i > 0$ iff all $x_i = 1$, and $k - 1 + \sum_i x_i > 0$ iff some $x_i = 1$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.3 p. 273, Lemma 20.4 with its proof

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 20.4** (p. 273). Suppose that a neuron `v`, that implements the sign activation
function, has `k` incoming edges, connecting it to neurons whose outputs are in `{±1}`. Then,
by adding one more edge, linking a "constant" neuron to `v`, and by adjusting the weights on
the edges to `v`, the output of `v` can implement the conjunction or the disjunction of its
inputs: `∧ᵢ xᵢ = sign(1 − k + ∑ᵢ xᵢ)` and `∨ᵢ xᵢ = sign(k − 1 + ∑ᵢ xᵢ)`. -/
theorem sign_and_or (k : ℕ) (x : Fin k → Bool) :
    (0 < 1 - (k : ℝ) + ∑ i, (if x i then (1 : ℝ) else -1) ↔ ∀ i, x i = true) ∧
    (0 < (k : ℝ) - 1 + ∑ i, (if x i then (1 : ℝ) else -1) ↔ ∃ i, x i = true) := by sorry

end UnderstandingML
