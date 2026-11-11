-- Prove2me | Theorems.Thm_PartialHomog_Threshold_removable_gate_replacement
-- name    : PartialHomog.Threshold.removable_gate_replacement
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:28:14.152998+00:00
-- url     : https://prove2.me/theorems/8b95ef02-c3b9-4ca0-ae97-6c73bb210e79
-- title:
--   §E.2 — removable product gates can be replaced by constants or sum gates without changing any gate's value
-- statement:
--   Let $\Phi$ be a division-free circuit over a commutative ring $R$. A product gate is removable if it computes $0$ or has at most one input edge carrying a non-constant polynomial (inputs counted with multiplicity). Such a gate can be replaced by a constant or by a sum gate: there is a circuit $\Psi$ with the same number of gates, in which every gate computes the same polynomial as in $\Phi$ and the output gates are the same, whose product gates are exactly the non-removable product gates of $\Phi$. In particular $\Psi$ has no removable product gate and
--   $$\#\{\text{product gates of }\Psi\}=\#\{\text{product gates of }\Phi\}-\#\{\text{removable gates of }\Phi\}.$$
--
--   This is why a circuit with the least number of product gates has no removable gate, the first step of the proof of Corollary E.14.
--
--   **Formalization Note** Gates of $\Psi$ and $\Phi$ are matched by `Fin.cast h` with `h : Ψ.size = Φ.size`.
--
--   Differences from the source:
--   - encoding: a circuit is a directed acyclic graph; product gates q_1, …, q_M in a topological order; unordered inputs of a product gate counted with multiplicity → a straight-line program `Circuit R N K`: gate t reads only gates < t, a product gate is a list of ≥ 2 earlier gate indices, product gates ordered by gate number; reason: every DAG has a topological order and a list with repeats is a multiset of inputs; the same circuits, the same polynomials and the same product-gate counts
--   - generalization: stated in §E.2 for the real circuits of Lemma E.13 / Corollary E.14 → any commutative ring R; reason: the replacement only uses that a product of constants is a constant; at R = ℝ it is the source's claim
--   - reading: 'Such a gate can be replaced by a constant or by a sum gate' → all removable gates replaced at once, every gate value and the outputs unchanged, the product gates of Ψ exactly the non-removable ones of Φ; reason: replacing a gate by one computing the same polynomial changes no value, so no other gate's removability changes; this is the form the proof of Corollary E.14 uses
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 26 (PDF 28), §E.2 (definition of removable gates)

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit
import Definitions.Def_PartialHomog_Threshold_ProductGates

open MvPolynomial

namespace PartialHomog.Threshold

/-- §E.2, removable product gates (p. 26): every removable product gate can be replaced by a
constant or by a sum gate. For every circuit `Φ` over a commutative ring there is a circuit `Ψ`
with the same gates (same number, every gate computing the same polynomial, same output gates)
whose product gates are exactly the non-removable product gates of `Φ`; in particular `Ψ` has no
removable product gate. -/
theorem removable_gate_replacement {R : Type*} [CommRing R] {N K : ℕ} (Φ : Circuit R N K) :
    ∃ Ψ : Circuit R N K, ∃ h : Ψ.size = Φ.size,
      (∀ t : Fin Ψ.size, Ψ.value t = Φ.value (Fin.cast h t)) ∧
      (∀ s : Fin K, Fin.cast h (Ψ.out s) = Φ.out s) ∧
      (∀ t : Fin Ψ.size,
        Ψ.IsProdGate t ↔ (Φ.IsProdGate (Fin.cast h t) ∧ ¬ Φ.IsRemovable (Fin.cast h t))) ∧
      ∀ t : Fin Ψ.size, ¬ Ψ.IsRemovable t := by sorry

end PartialHomog.Threshold
