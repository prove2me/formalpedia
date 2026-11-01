-- Prove2me | Theorems.Thm_SymTensorNet_eq_15
-- name    : SymTensorNet.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:21:20.685618+00:00
-- url     : https://prove2.me/theorems/ca172ef5-fc42-4931-830d-6b0ea8a869eb
-- title:
--   Eq. (15) — every symmetric tensor decomposes uniquely into degeneracy tensors and structural tensors along any trivalent tree
-- statement:
--   Let $G$ be a group, with a catalogue of irreps $U^a$, fusion data (Clebsch–Gordan isometries) and conjugation data ($\bar a$, $J^a$). Let $T$ be a tensor with a finite set of legs $i_s=(a_s,\alpha_{a_s},m_{a_s})$, $s=1,\dots,t$, each outgoing or incoming, with arbitrary finite degeneracy spaces, and fix a root leg $r$. For a fusion tree $\tau$ valid for $r$ (every other leg a leaf exactly once) and charges $a=(a_s)$, let $L(\tau,r,a)$ be the labellings of the inner branches by intermediate charges $e_1,\dots,e_{t'}$ (and channels) that fuse to the root, and $Q(a,\ell)$ ($\ell\in L(\tau,r,a)$) the structural tensors, which depend only on the symmetry data, the directions, the charges and the tree. Then:
--
--   1. **(decomposition)** For every valid tree $\tau$ and all degeneracy spaces, every family of degeneracy tensors $P$ (unconstrained) gives a symmetric tensor
--   $$T_{i_1\dots i_t}=\sum_{\ell\in L(\tau,r,a)}\big(P^{a_1\dots a_t}_{\ell}\big)_{\alpha_{a_1}\dots\alpha_{a_t}}\big(Q^{a_1\dots a_t}_{\ell}\big)_{m_{a_1}\dots m_{a_t}},$$
--   and every symmetric tensor is of this form for exactly one $P$. So $P$ contains all the degrees of freedom of $T$ and $Q$ is completely determined by the symmetry.
--   2. **(change of tree)** For any two trees $\tau,\tilde\tau$ valid for $r$ there are unitary matrices $F(a)$, with rows $L(\tau,r,a)$ and columns $L(\tilde\tau,r,a)$, fixed before any degeneracy space or tensor is chosen, such that
--   $$\tilde Q(a,\tilde\ell)=\sum_\ell F(a)_{\ell\tilde\ell}\,Q(a,\ell),$$
--   and whenever $\tau$ with degeneracy tensors $P$ and $\tilde\tau$ with $\tilde P$ give the same tensor,
--   $$\tilde P(\alpha,\tilde\ell)=\sum_\ell\overline{F(a)_{\ell\tilde\ell}}\,P(\alpha,\ell).$$
--
--   With the root incoming and all other legs outgoing, $Q$ is the paper's: $\delta_{ab}\delta_{m_an_b}$ for $t=2$ (Eq. (8)), Clebsch–Gordan coefficients for $t=3$ (Eq. (10)), and Eqs. (11)–(12) for $t=4$, whose relation is Eqs. (13)–(14).
--
--   **Formalization Note** Incoming legs enter the tree with the conjugate charge $\bar a$ through $\overline{J^a}$, and an outgoing root through $J^a$; with an incoming root and outgoing other legs no $J$ appears.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness only supplies complete reducibility, which unitarity gives; compact groups are an instance.
--   - generalization: G multiplicity free, inner branches labelled by intermediate charges e_k → labelled by fusion channels; reason: footnote [10]; with multiplicity freeness a channel is determined by its charge, which is the printed form.
--   - reading: the sum over (e_k, α_{e_k}, m_{e_k}) with α_{e_k} an index of P and m_{e_k} an index of Q → m_{e_k} contracted inside Q, no index α_{e_k}; reason: below Eq. (12) Q̃ is written without r_f, the coupled basis |dp_d; e⟩ of Eq. (11) carries no q_e, Fig. 2(iv) puts the inner edge only in the structural part; an index α_{e_k} would make P non-unique.
--   - reading: "decomposes as … P contain all the degrees of freedom of T, whereas Q are completely determined by the symmetry" → P ↦ T is a bijection from unconstrained P onto the symmetric tensors, with Q defined from the symmetry data alone; reason: existence alone would lose the clause on degrees of freedom.
--   - reading: "a different choice of tree will produce P̃ and Q̃, related to P and Q by F-moves" → for two trees with the same root, a unitary F(a), depending only on the symmetry data and the charges, with Q̃ = Σ F Q and P̃ = Σ F* P; reason: this is what Eqs. (13)–(14) assert for one move; across different roots the change of basis is not unitary, so the root is shared.
--   - reading: t′ (not defined in the paper) → the number of inner branches of the tree; reason: it gives t′ = 0 for Eq. (10) and t′ = 1 for Eq. (11).
--   - generalization: trivalent trees → trees that may also have trivial leaves (charge 0); reason: needed for t = 1 ("One leg"); trees without trivial leaves are an instance.
--   - encoding: incoming legs and the outgoing/incoming root → a root leg r, a conjugate charge ā and a unitary J^a with J^a conj(U^a_g) = U^ā_g J^a; reason: incoming legs carry the conjugate representation (Eq. (7)); with an incoming root and outgoing other legs J does not appear and Q is the paper's.
--   - encoding: index i_s = (a_s, α_{a_s}, m_{a_s}) → a pair (α, m) with α in a finite set of labels with charges; reason: 𝔻^a has basis {α : chg(α) = a}; same instances.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (15) and the paragraph after it, p.3; footnote [10], p.4

import Mathlib
import Definitions.Def_SymTensorNet_StructuralTensor

namespace SymTensorNet

universe u v w z

open Matrix

/-- **Eq. (15): every symmetric tensor decomposes uniquely into degeneracy tensors and structural
tensors along any trivalent tree, and two trees are related by a unitary fixed by the symmetry.**

For every group `G`, every catalogue of irreps with fusion data `F` and conjugation data `K`, every
finite set of legs `S` with directions `dir` and root leg `r`:
1. for every tree `τ` valid for `r` and all degeneracy spaces, every degeneracy family `P` gives a
   symmetric tensor `synth P`, and every symmetric tensor `T` equals `synth P` for exactly one `P`;
2. for all trees `τ, τ̃` valid for `r` there are unitary matrices `F(a)` (rows `L(τ, r, a)`, columns
   `L(τ̃, r, a)`), chosen before any degeneracy space or tensor, with
   `Q̃(a, ℓ̃) = Σ_ℓ F(a)_{ℓ ℓ̃} Q(a, ℓ)`, and such that `synth_τ P = synth_τ̃ P̃` forces
   `P̃(α, ℓ̃) = Σ_ℓ conj(F(a)_{ℓ ℓ̃}) P(α, ℓ)`.

arXiv:0907.2994v2, Eq. (15), p.3, with the sentences after it ("The degeneracy tensors … contain
all the degrees of freedom of T, whereas the structural tensors … are completely determined by the
symmetry … A different choice of tree will produce different sets of tensors P̃ and Q̃, related to P
and Q by F-moves").

**Formalization Note** `G` is a bare group (compactness is dropped) and fusion is through channels
(multiplicity freeness is dropped, footnote [10]). Incoming legs enter the tree through the
conjugation unitaries `J` of `K`; with an incoming root and outgoing other legs `J` does not
appear. The intermediate index `q_e` is contracted inside `Q` and no intermediate degeneracy index
`ϵ_e` is carried by `P`. -/
theorem eq_15 {G : Type u} [Group G] (F : FusionData.{u, v} G) (K : ConjData F.toIrrepCatalogue) {S : Type w} [Fintype S] [DecidableEq S] (dir : S → Dir) (r : S) : (∀ τ : Tree S, IsValidTree τ r → ∀ {Deg : S → Type z} [∀ s, Fintype (Deg s)] [∀ s, DecidableEq (Deg s)] (chg : (s : S) → Deg s → F.Charge), (∀ P : (α : (s : S) → Deg s) → AdmLab F K dir τ r (fun s => chg s (α s)) → ℂ, IsSymmetric F.toIrrepCatalogue dir chg (synth F K dir τ r chg P)) ∧ (∀ T : ((s : S) → LegIdx F.toIrrepCatalogue chg s) → ℂ, IsSymmetric F.toIrrepCatalogue dir chg T → ∃! P : (α : (s : S) → Deg s) → AdmLab F K dir τ r (fun s => chg s (α s)) → ℂ, synth F K dir τ r chg P = T)) ∧ (∀ τ τ' : Tree S, IsValidTree τ r → IsValidTree τ' r → ∃ Fm : (a : S → F.Charge) → Matrix (AdmLab F K dir τ r a) (AdmLab F K dir τ' r a) ℂ, (∀ a, Fm a * (Fm a)ᴴ = 1 ∧ (Fm a)ᴴ * Fm a = 1) ∧ (∀ (a : S → F.Charge) (ℓ' : AdmLab F K dir τ' r a) (m : (s : S) → Fin (F.dim (a s))), structQ F K dir τ' r a ℓ' m = ∑ ℓ : AdmLab F K dir τ r a, Fm a ℓ ℓ' * structQ F K dir τ r a ℓ m) ∧ (∀ {Deg : S → Type z} [∀ s, Fintype (Deg s)] [∀ s, DecidableEq (Deg s)] (chg : (s : S) → Deg s → F.Charge) (P : (α : (s : S) → Deg s) → AdmLab F K dir τ r (fun s => chg s (α s)) → ℂ) (P' : (α : (s : S) → Deg s) → AdmLab F K dir τ' r (fun s => chg s (α s)) → ℂ), synth F K dir τ r chg P = synth F K dir τ' r chg P' → ∀ (α : (s : S) → Deg s) (ℓ' : AdmLab F K dir τ' r (fun s => chg s (α s))), P' α ℓ' = ∑ ℓ : AdmLab F K dir τ r (fun s => chg s (α s)), star (Fm (fun s => chg s (α s)) ℓ ℓ') * P α ℓ)) := by sorry

end SymTensorNet
