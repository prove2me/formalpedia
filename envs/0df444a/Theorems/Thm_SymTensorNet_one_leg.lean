-- Prove2me | Theorems.Thm_SymTensorNet_one_leg
-- name    : SymTensorNet.one_leg
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:24.807041+00:00
-- url     : https://prove2.me/theorems/e20e7bcb-1afa-41dd-b3e1-62f5fa661e47
-- title:
--   One leg — a one-index symmetric tensor lives on the trivial charge
-- statement:
--   Let $\{U^a\}$ be a catalogue of pairwise inequivalent irreps of a group $G$ containing the trivial charge $0$ ($\dim 0=1$, $U^0_g=1$). Let $T$ be a tensor with a single leg, outgoing or incoming, with index $i=(a,\alpha_a,m_a)$. Then $T$ is symmetric if and only if
--   $$T_{(a,\alpha_a,m_a)}=0\qquad\text{whenever }a\neq 0 .$$
--   So the only relevant irrep is $a=0$, the index reduces to $i=\alpha_0$, a label of the degeneracy space of the trivial irrep, and every vector of that space is a symmetric tensor.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: no property of compact groups is used; compact groups are an instance.
--   - reading: "invariant only if G acts on it trivially, so the only relevant irrep is a = 0, and index i = α_0 labels states within the degeneracy space" → T symmetric if and only if T vanishes off charge 0; reason: "labels states within the degeneracy space" says every such state is allowed; the equivalence is the stronger reading.
--   - encoding: the trivial charge → a charge z with dim z = 1 and U^z_g = 1, given as a hypothesis; reason: the paper's convention a = 0; same instances.
--   - encoding: index i = (a, α_a, m_a) → a pair (α, m) with α in a finite set of labels with charges; reason: 𝔻^a has basis {α : chg(α) = a}; same instances.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, One leg, p.2

import Mathlib
import Definitions.Def_SymTensorNet_SymmetricTensor

namespace SymTensorNet

universe u v w

open Matrix

/-- **One leg: only the trivial charge is relevant.** Let `C` be a catalogue of irreps of `G` with
a trivial charge `0` (`dim 0 = 1`, `U⁰_g = 1`). A tensor `T` with a single leg, of either
direction, is symmetric if and only if it vanishes on every index `(α, m)` whose charge is not
`0`. So the index of a one-leg symmetric tensor is `i = α₀`, a label of the degeneracy space of
the trivial irrep, and every vector of that degeneracy space is allowed.

arXiv:0907.2994v2, p.2, "One leg".

**Formalization Note** The single leg is the leg set `Unit`; `G` is a bare group. -/
theorem one_leg {G : Type u} [Group G] (C : IrrepCatalogue.{u, v} G) (z : C.Charge) (hz1 : C.dim z = 1) (hz : ∀ g : G, (C.rep z g : Matrix (Fin (C.dim z)) (Fin (C.dim z)) ℂ) = 1) (d : Dir) {D : Type w} [Fintype D] [DecidableEq D] (chg : D → C.Charge) (T : ((s : Unit) → LegIdx C (Deg := fun _ => D) (fun _ => chg) s) → ℂ) : IsSymmetric C (fun _ => d) (Deg := fun _ => D) (fun _ => chg) T ↔ ∀ i : (s : Unit) → LegIdx C (Deg := fun _ => D) (fun _ => chg) s, chg (i ()).1 ≠ z → T i = 0 := by sorry

end SymTensorNet
