-- Prove2me | Theorems.Thm_QThermalClassical_lemma_7
-- name    : QThermalClassical.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:20.270797+00:00
-- url     : https://prove2.me/theorems/a8faaf10-99a6-49bc-a785-6d4e24d08a67
-- title:
--   Lemma 7 — separable Pauli factors
-- statement:
--   Let $\rho$ be an operator on $n$ qubits that can be expressed as
--   $$
--   \rho=\sum_ip_i\bigotimes_l\left(I+c_{i,l}P_{i,l}\right)\qquad(49),
--   $$
--   where $p_i\ge0$, each $P_{i,l}$ is a Pauli string on block $l$, the blocks are disjoint, and $c_{i,l}\in\mathbb R$ with $|c_{i,l}|\le1$. Then $\rho$ is separable into a mixture of stabilizer states: it is a nonnegative combination of tensor products of the single-qubit stabilizer states $\tfrac12(I\pm X)$, $\tfrac12(I\pm Y)$, $\tfrac12(I\pm Z)$.
--
--   This is the last step of the separability proof: the pinning procedure writes $e^{-\beta H}$ in the form (49).
--
--   Differences from the source:
--   - generalization: a positive operator $\rho$ → no positivity hypothesis; reason: positivity follows from the conclusion
--   - generalization: $\sum_i$ over a finite or countable index → a convergent (unconditional) sum over any index type; reason: covers both; the cone of the conclusion is finitely generated, hence closed
--   - reading: "separable into a mixture of stabilizer states" → a nonnegative combination of tensor products of the six single-qubit stabilizer states; reason: the decomposition (52) and the proof's last sentence
--   - encoding: $P_{i,l}$ a Pauli product on block $l$, blocks disjoint, $\bigotimes_l$ → Pauli words with pairwise disjoint supports and the ordinary product of the factors; reason: a block containing each support exists; on disjoint blocks the tensor product is the product
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 7, eq. (49), p.19; eq. (52), p.20

import Mathlib
import Definitions.Def_QThermalClassical_PauliProductCone

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 7 (Separable Pauli factors).** If `ρ = Σ_i p_i ⊗_l (I + c_{i,l} P_{i,l})` with
`p_i ≥ 0`, Pauli strings `P_{i,l}` on disjoint blocks, and real `|c_{i,l}| ≤ 1`, then `ρ` is a
nonnegative combination of products of single-qubit stabilizer states.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 7, eq. (49), p.19; eq. (52), p.20.

**Formalization Note.** The index set `ι` is any type and the sum is a `HasSum` (covering
finite and countable mixtures). For each `i` the factors are a finite list of pairs
`(c_{i,l}, P_{i,l})` whose word supports are pairwise disjoint; the tensor product over
disjoint blocks is the ordinary product. The hypothesis "positive operator" is dropped: it
follows from the conclusion. -/
theorem lemma_7 {Q : Type} [Fintype Q] [DecidableEq Q] {ι : Type} (p : ι → ℝ)
    (fac : ι → List (ℝ × PauliWord Q)) (ρ : Op Q)
    (hp : ∀ i, 0 ≤ p i)
    (hc : ∀ i, ∀ f ∈ fac i, |f.1| ≤ 1)
    (hdisj : ∀ i, (fac i).Pairwise fun f g => Disjoint (pauliSupport f.2) (pauliSupport g.2))
    (hρ : HasSum (fun i => ((p i : ℝ) : ℂ) •
      ((fac i).map fun f => (1 : Op Q) + ((f.1 : ℝ) : ℂ) • pauliOp f.2).prod) ρ) :
    PauliProductCone ρ := by sorry

end QThermalClassical
