-- Prove2me | Theorems.Thm_PhaseEncodedQGE_layer_occupancy
-- name    : PhaseEncodedQGE.layer_occupancy
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:51:43.455351+00:00
-- url     : https://prove2.me/theorems/6429ee3e-e612-4dfa-a71a-2a54bdee0d6e
-- title:
--   §2 — for small $\beta$ the $m$-defect layer occupies the $m$-defect block
-- statement:
--   Fix $n$, angles with $0<\eta<\pi$ and $t=\tan(\eta/2)>1$, a mixer axis and a number of repetitions. There is $\beta_0>0$ such that for every $\beta\in(0,\beta_0)$, every cubic graph $G$ on $n$ vertices with the degree-aware preparation and every $m$, the entries of the sorted readout at the ranks $K_{m-1}(n)+1,\dots,K_m(n)$ are exactly the Born probabilities $p_G(x;\beta)$ of the outcomes with $m$ defects, in descending order:
--   $$\bigl(p^\downarrow_G\bigr)_{K_{m-1}(n)+1..K_m(n)}=\operatorname{sort}_{\downarrow}\{\!\{p_G(x;\beta):|D(x)|=m\}\!\}.$$
--
--   This is what makes the $m$-defect block of the sorted readout a readout of the $m$-defect layer.
--
--   Differences from the source:
--   - generalization: the degree-prepared members PE-X1, PE-Y1, PE-X2 → every mixer axis P and every number r of repetitions; reason: the argument (layer weights separated by t^{-2}, Born probabilities continuous in β) uses no property of the member; it specializes to the paper's members
--   - encoding: for $\beta$ small enough (for a given graph and layer) → one $\beta_0>0$ chosen before the cubic graph and the layer; reason: finitely many graphs on Fin n and finitely many nonempty layers, so the uniform and the per-graph readings are the same claim
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §2, p.5 (PDF p.6), 'Defect layers and blocks'

import Mathlib
import Definitions.Def_PhaseEncodedQGE_SortedReadout
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Layer occupancy (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §2, p.5, "Defect layers and blocks").

Fix the degree-aware preparation on cubic graphs with `0 < η < π` and `t = tan(η/2) > 1`. For `β`
small enough the `m`-defect layer occupies the `m`-defect block: the entries of the sorted readout
at the ranks `K_{m−1}(n) + 1, …, K_m(n)` are exactly the Born probabilities `p_G(x; β)` of the
outcomes with `m` defects, in descending order.

**Formalization Note** The threshold `β₀` is chosen before the graph and the layer, which for fixed
`n` is equivalent to choosing it per graph (there are finitely many graphs on `Fin n` and finitely
many nonempty layers). The statement is made for every mixer axis and every `r`. -/
theorem layer_occupancy (n : ℕ) (η γ : ℝ) (hη0 : 0 < η) (hηπ : η < Real.pi)
    (ht : 1 < Real.tan (η / 2)) (P : Axis) (r : ℕ) :
    ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G : SimpleGraph (Fin n), IsCubic G → ∀ m : ℕ,
      block (degPrep G η) P r G γ β m =
        (((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
          (born (degPrep G η) P r G γ β)).sort (· ≥ ·) := by sorry

end PhaseEncodedQGE
