-- Prove2me | Theorems.Thm_SymTensorNet_eq_10
-- name    : SymTensorNet.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:21.294153+00:00
-- url     : https://prove2.me/theorems/1d4df0d0-bf83-406f-ae72-9e7c133d4205
-- title:
--   Eq. (10) — Wigner–Eckart theorem, $T_{ijk}=(P^{abc})_{\alpha_a\beta_b\gamma_c}(Q^{abc})_{m_an_bo_c}$
-- statement:
--   Let $G$ be a group with fusion data for a catalogue of irreps. Consider tensors with two outgoing legs $i=(a,\alpha_a,m_a)$, $j=(b,\beta_b,n_b)$ and one incoming leg $k=(c,\gamma_c,o_c)$, with arbitrary finite degeneracy spaces. Then
--   1. for every family of degeneracy tensors $P$, the tensor
--   $$T_{ijk}=\sum_{\kappa}(P^{abc}_\kappa)_{\alpha_a\beta_b\gamma_c}(Q^{abc}_\kappa)_{m_an_bo_c},$$
--   with $\kappa$ running over the channels of $a\otimes b$ with output $c$ and $Q^{abc}_\kappa$ their Clebsch–Gordan coefficients, is symmetric;
--   2. every symmetric tensor $T$ is of this form for exactly one $P$.
--
--   When $G$ is multiplicity free there is at most one channel, and this is $T_{ijk}=(P^{abc})_{\alpha_a\beta_b\gamma_c}(Q^{abc})_{m_an_bo_c}$: for fixed charges, $T$ factorizes into a degeneracy tensor $P^{abc}$, which holds all the degrees of freedom, and the structural tensor $Q^{abc}$, which is fixed by the group.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness only supplies complete reducibility, which unitarity gives; compact groups are an instance.
--   - generalization: G multiplicity free, one term (P^{abc})(Q^{abc}) → a sum over the channels κ of a ⊗ b with output c; reason: footnote [10]; with multiplicity freeness the sum has at most one term, which is the printed form.
--   - reading: "decomposes as" (10), with "P^{abc} with all the degrees of freedom" (p.3) → every P gives a symmetric tensor and every symmetric tensor has exactly one P; reason: the sentence on p.3 says P is unconstrained and determined by T; existence alone would drop it.
--   - encoding: index (a, α_a, m_a) → a pair (α, m) with α in a finite set of labels with charges; reason: 𝔻^a has basis {α : chg(α) = a}; same instances.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (10), p.2, and "As before, for fixed values of the charges a, b, c", p.3

import Mathlib
import Definitions.Def_SymTensorNet_FewLegs

namespace SymTensorNet

universe u v w

open Matrix

/-- **Eq. (10): Wigner–Eckart theorem for three legs.** For a tensor with two outgoing legs
`i = (a, α, m)`, `j = (b, β, n)` and one incoming leg `k = (c, γ, o)`: every family of degeneracy
tensors `P` gives a symmetric tensor
`T_{ijk} = Σ_κ (P^{abc}_κ)_{α β γ} (Q^{abc}_κ)_{m n o}` (sum over the channels `κ` of `a ⊗ b` with
output `c`), and every symmetric tensor is of this form for exactly one `P`. When `G` is
multiplicity free the sum has at most one term, as printed.

arXiv:0907.2994v2, p.2, Eq. (10), and p.3 ("for fixed values of the charges a, b, c, (T)_{ijk}
factorizes into degeneracy tensors P^{abc} with all the degrees of freedom and structural tensors
Q^{abc} … completely determined by the group").

**Formalization Note** `G` is a bare group, and the multiplicity index of footnote [10] is the
channel `κ`. -/
theorem eq_10 {G : Type u} [Group G] (F : FusionData.{u, v} G) {Deg : Fin 3 → Type w} [∀ s, Fintype (Deg s)] [∀ s, DecidableEq (Deg s)] (chg : (s : Fin 3) → Deg s → F.Charge) : (∀ P : (α : (s : Fin 3) → Deg s) → Chan10 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) → ℂ, IsSymmetric F.toIrrepCatalogue dir3 chg (synth10 F chg P)) ∧ (∀ T : ((s : Fin 3) → LegIdx F.toIrrepCatalogue chg s) → ℂ, IsSymmetric F.toIrrepCatalogue dir3 chg T → ∃! P : (α : (s : Fin 3) → Deg s) → Chan10 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) → ℂ, synth10 F chg P = T) := by sorry

end SymTensorNet
