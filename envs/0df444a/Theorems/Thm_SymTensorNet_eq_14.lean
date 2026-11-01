-- Prove2me | Theorems.Thm_SymTensorNet_eq_14
-- name    : SymTensorNet.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:12.294592+00:00
-- url     : https://prove2.me/theorems/686c1e62-b93f-463a-89ba-041078c10390
-- title:
--   Eq. (14) — the degeneracy tensors transform by $F^*$, $\tilde P^{abcd}_f=\sum_e(F^{abc*}_d)^e_fP^{abcd}_e$
-- statement:
--   Let $G$ be a group with fusion data for a catalogue of irreps, and for all charges $a,b,c,d$ let $F^{abc}_d$ be a unitary matrix with $\tilde Q^{abcd}_f=\sum_e(F^{abc}_d)^e_fQ^{abcd}_e$ (Eq. (13)). Consider four-leg tensors with legs $i,j,k$ outgoing and $l$ incoming. If the decompositions of Eq. (11), with degeneracy tensors $P$, and of Eq. (12), with degeneracy tensors $\tilde P$, represent the same tensor $T$, then
--   $$\tilde P^{abcd}_f=\sum_e\big(F^{abc*}_d\big)^e_f\,P^{abcd}_e$$
--   for all charges and all degeneracy indices, where $^*$ is complex conjugation.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness only supplies complete reducibility, which unitarity gives; compact groups are an instance.
--   - generalization: G multiplicity free, labels e, f intermediate charges → labels pairs of channels; reason: footnote [10]; with multiplicity freeness the labels are the intermediate charges.
--   - encoding: index (a, α_a, m_a) → a pair (α, m) with α in a finite set of labels with charges; reason: 𝔻^a has basis {α : chg(α) = a}; same instances.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (14) and the sentence before it, p.3

import Mathlib
import Definitions.Def_SymTensorNet_FewLegs

namespace SymTensorNet

universe u v w

open Matrix

/-- **Eq. (14): the degeneracy tensors transform with `F*`.** Let `F^{abc}_d` be, for all charges,
the unitary matrices of Eq. (13) (`Q̃^{abcd}_f = Σ_e (F^{abc}_d)^e_f Q^{abcd}_e`). If the
decompositions of Eqs. (11) and (12) represent the same tensor `T`, then the degeneracy tensors
are related by `P̃^{abcd}_f = Σ_e ((F^{abc}_d)^e_f)* P^{abcd}_e`.

arXiv:0907.2994v2, p.3, Eq. (14) ("Since Eqs. 11 and 12 represent the same tensor T, the
degeneracy tensors P and P̃ are related by").

**Formalization Note** `G` is a bare group; the labels `e`, `f` are pairs of channels
(footnote [10]). -/
theorem eq_14 {G : Type u} [Group G] (F : FusionData.{u, v} G) (Fm : (a b c d : F.Charge) → Matrix (Lab11 F a b c d) (Lab12 F a b c d) ℂ) (hFm : ∀ a b c d : F.Charge, Fm a b c d * (Fm a b c d)ᴴ = 1 ∧ (Fm a b c d)ᴴ * Fm a b c d = 1 ∧ ∀ (f : Lab12 F a b c d) (m : Fin (F.dim a)) (n : Fin (F.dim b)) (o : Fin (F.dim c)) (p : Fin (F.dim d)), Q12 F f m n o p = ∑ e : Lab11 F a b c d, Fm a b c d e f * Q11 F e m n o p) {Deg : Fin 4 → Type w} [∀ s, Fintype (Deg s)] [∀ s, DecidableEq (Deg s)] (chg : (s : Fin 4) → Deg s → F.Charge) (P : (α : (s : Fin 4) → Deg s) → Lab11 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ) (P' : (α : (s : Fin 4) → Deg s) → Lab12 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ) (hT : synth11 F chg P = synth12 F chg P') : ∀ (α : (s : Fin 4) → Deg s) (f : Lab12 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3))), P' α f = ∑ e : Lab11 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)), star (Fm (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) e f) * P α e := by sorry

end SymTensorNet
