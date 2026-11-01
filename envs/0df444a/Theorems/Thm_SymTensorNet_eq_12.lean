-- Prove2me | Theorems.Thm_SymTensorNet_eq_12
-- name    : SymTensorNet.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:52.991836+00:00
-- url     : https://prove2.me/theorems/8232b59b-f759-43db-8dcc-8a9921462c5c
-- title:
--   Eq. (12) — four legs, fusing $b$ and $c$ first
-- statement:
--   Let $G$ be a group with fusion data for a catalogue of irreps. Consider tensors with three outgoing legs $i=(a,\alpha_a,m_a)$, $j=(b,\beta_b,n_b)$, $k=(c,\gamma_c,o_c)$ and one incoming leg $l=(d,\delta_d,p_d)$, with arbitrary finite degeneracy spaces. Let $f$ run over the labels of the coupled basis $|dp_d;f\rangle$ of $\mathbb V^d$ obtained by fusing first $b$ and $c$ into $f$ and then $a$ and $f$ into $d$, and let
--   $$(\tilde Q^{abcd}_f)_{m_an_bo_cp_d}=\sum_{r_f}(Q^{bcf})_{n_bo_cr_f}(Q^{afd})_{m_ar_fp_d}$$
--   be the change of basis to that coupled basis. Then
--   1. for every family of degeneracy tensors $\tilde P$, the tensor
--   $$T_{ijkl}=\sum_{f}(\tilde P^{abcd}_f)_{\alpha_a\beta_b\gamma_c\delta_d}(\tilde Q^{abcd}_f)_{m_an_bo_cp_d}$$
--   is symmetric;
--   2. every symmetric tensor $T$ is of this form for exactly one $\tilde P$.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness only supplies complete reducibility, which unitarity gives; compact groups are an instance.
--   - generalization: G multiplicity free, f an intermediate charge → f a pair of channels (b ⊗ c → f, a ⊗ f → d); reason: footnote [10]; with multiplicity freeness the pair is determined by the intermediate charge.
--   - reading: the sum over (f, ζ_f, r_f) with ζ_f an index of P̃ and r_f an index of Q̃ → r_f contracted inside Q̃^{abcd}_f, no index ζ_f; reason: the paper itself writes (Q̃^{abcd}_f)_{m_a n_b o_c p_d} without r_f below Eq. (12); Fig. 2(iv); an index ζ_f would make P̃ non-unique.
--   - reading: "can be decomposed as" → every P̃ gives a symmetric tensor and every symmetric tensor has exactly one P̃; reason: P̃ holds all the degrees of freedom (p.3, Eq. (15)), and Eq. (14) presupposes its uniqueness.
--   - encoding: index (a, α_a, m_a) → a pair (α, m) with α in a finite set of labels with charges; reason: 𝔻^a has basis {α : chg(α) = a}; same instances.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (12) and the sentence after it, p.3

import Mathlib
import Definitions.Def_SymTensorNet_FewLegs

namespace SymTensorNet

universe u v w

open Matrix

/-- **Eq. (12): four legs, fusing `b` and `c` first.** For a tensor with three outgoing legs
`i = (a, α, m)`, `j = (b, β, n)`, `k = (c, γ, o)` and one incoming leg `l = (d, δ, p)`: every
family of degeneracy tensors `P̃` gives a symmetric tensor
`T_{ijkl} = Σ_f (P̃^{abcd}_f)_{α β γ δ} (Q̃^{abcd}_f)_{m n o p}`, where `f` runs over the coupled
basis labels (intermediate charge `f` of `b ⊗ c`, then `a ⊗ f → d`) and
`(Q̃^{abcd}_f)_{m n o p} = Σ_r Q^{bcf}_{n o r} Q^{afd}_{m r p}`; and every symmetric tensor is of
this form for exactly one `P̃`.

arXiv:0907.2994v2, p.3, Eq. (12).

**Formalization Note** The intermediate index `r_f` is contracted inside `Q̃^{abcd}_f`, and `P̃`
carries no intermediate degeneracy index `ζ_f`. `G` is a bare group, and each fusion step is a
channel (footnote [10]). -/
theorem eq_12 {G : Type u} [Group G] (F : FusionData.{u, v} G) {Deg : Fin 4 → Type w} [∀ s, Fintype (Deg s)] [∀ s, DecidableEq (Deg s)] (chg : (s : Fin 4) → Deg s → F.Charge) : (∀ P : (α : (s : Fin 4) → Deg s) → Lab12 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ, IsSymmetric F.toIrrepCatalogue dir4 chg (synth12 F chg P)) ∧ (∀ T : ((s : Fin 4) → LegIdx F.toIrrepCatalogue chg s) → ℂ, IsSymmetric F.toIrrepCatalogue dir4 chg T → ∃! P : (α : (s : Fin 4) → Deg s) → Lab12 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ, synth12 F chg P = T) := by sorry

end SymTensorNet
