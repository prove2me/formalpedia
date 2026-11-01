-- Prove2me | Theorems.Thm_SymTensorNet_eq_11
-- name    : SymTensorNet.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:24.095987+00:00
-- url     : https://prove2.me/theorems/228c11a1-cc75-430a-8f65-f7c8a597a786
-- title:
--   Eq. (11) — four legs, fusing $a$ and $b$ first
-- statement:
--   Let $G$ be a group with fusion data for a catalogue of irreps. Consider tensors with three outgoing legs $i=(a,\alpha_a,m_a)$, $j=(b,\beta_b,n_b)$, $k=(c,\gamma_c,o_c)$ and one incoming leg $l=(d,\delta_d,p_d)$, with arbitrary finite degeneracy spaces. Let $e$ run over the labels of the coupled basis $|dp_d;e\rangle$ obtained by fusing $a$ and $b$ into an intermediate charge $e$ and then $e$ and $c$ into $d$, and let
--   $$(Q^{abcd}_e)_{m_an_bo_cp_d}=\sum_{q_e}(Q^{abe})_{m_an_bq_e}(Q^{ecd})_{q_eo_cp_d}$$
--   be the change of basis to that coupled basis. Then
--   1. for every family of degeneracy tensors $P$, the tensor
--   $$T_{ijkl}=\sum_{e}(P^{abcd}_e)_{\alpha_a\beta_b\gamma_c\delta_d}(Q^{abcd}_e)_{m_an_bo_cp_d}$$
--   is symmetric;
--   2. every symmetric tensor $T$ is of this form for exactly one $P$.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness only supplies complete reducibility, which unitarity gives; compact groups are an instance.
--   - generalization: G multiplicity free, e an intermediate charge → e a pair of channels (a ⊗ b → e, e ⊗ c → d); reason: footnote [10]; with multiplicity freeness the pair is determined by the intermediate charge.
--   - reading: the sum over (e, ϵ_e, q_e) with ϵ_e an index of P and q_e an index of Q → q_e contracted inside Q^{abcd}_e, no index ϵ_e; reason: the coupled basis |dp_d; e⟩ carries no q_e, below Eq. (12) Q̃ is written without r_f, and in Fig. 2(iv) only the structural part has the inner edge; an index ϵ_e would make P non-unique.
--   - reading: "decomposes as" → every P gives a symmetric tensor and every symmetric tensor has exactly one P; reason: P holds "all the degrees of freedom" (p.3, Eq. (15)); existence alone would drop it.
--   - encoding: index (a, α_a, m_a) → a pair (α, m) with α in a finite set of labels with charges; reason: 𝔻^a has basis {α : chg(α) = a}; same instances.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (11), p.3

import Mathlib
import Definitions.Def_SymTensorNet_FewLegs

namespace SymTensorNet

universe u v w

open Matrix

/-- **Eq. (11): four legs, fusing `a` and `b` first.** For a tensor with three outgoing legs
`i = (a, α, m)`, `j = (b, β, n)`, `k = (c, γ, o)` and one incoming leg `l = (d, δ, p)`: every
family of degeneracy tensors `P` gives a symmetric tensor
`T_{ijkl} = Σ_e (P^{abcd}_e)_{α β γ δ} (Q^{abcd}_e)_{m n o p}`, where `e` runs over the coupled
basis labels (intermediate charge `e` of `a ⊗ b`, then `e ⊗ c → d`) and
`(Q^{abcd}_e)_{m n o p} = Σ_q Q^{abe}_{m n q} Q^{ecd}_{q o p}`; and every symmetric tensor is of
this form for exactly one `P`.

arXiv:0907.2994v2, p.3, Eq. (11).

**Formalization Note** The intermediate index `q_e` is contracted inside `Q^{abcd}_e`, and `P`
carries no intermediate degeneracy index `ϵ_e`. `G` is a bare group, and each fusion step is a
channel (footnote [10]). -/
theorem eq_11 {G : Type u} [Group G] (F : FusionData.{u, v} G) {Deg : Fin 4 → Type w} [∀ s, Fintype (Deg s)] [∀ s, DecidableEq (Deg s)] (chg : (s : Fin 4) → Deg s → F.Charge) : (∀ P : (α : (s : Fin 4) → Deg s) → Lab11 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ, IsSymmetric F.toIrrepCatalogue dir4 chg (synth11 F chg P)) ∧ (∀ T : ((s : Fin 4) → LegIdx F.toIrrepCatalogue chg s) → ℂ, IsSymmetric F.toIrrepCatalogue dir4 chg T → ∃! P : (α : (s : Fin 4) → Deg s) → Lab11 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ, synth11 F chg P = T) := by sorry

end SymTensorNet
