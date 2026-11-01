-- Prove2me | Theorems.Thm_SymTensorNet_eq_4_5
-- name    : SymTensorNet.eq_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:32.4386+00:00
-- url     : https://prove2.me/theorems/8c9e14df-7125-4e55-be95-2460a44a50d7
-- title:
--   Eqs. (4)–(5) — a unitary representation decomposes into labelled irreps, $U_g=\bigoplus_a(\mathbb I^a\otimes U^a_g)$
-- statement:
--   Let $G$ be a group, $U:G\to U(N)$ a unitary matrix representation on $\mathbb V=\mathbb C^N$, and $\{U^a\}$ a catalogue of pairwise inequivalent irreps of $G$ that covers $U$ (every irrep occurring in $U$ is equivalent to some $U^a$). Then there are a finite set of degeneracy labels $\alpha$, a charge $\mathrm{chg}(\alpha)$ for each label, and a unitary matrix $V$ from $\bigoplus_\alpha\mathbb V^{\mathrm{chg}(\alpha)}$ to $\mathbb C^N$ such that
--   $$V^\dagger U_g V=\bigoplus_\alpha U^{\mathrm{chg}(\alpha)}_g\qquad\text{for all }g\in G.$$
--   Grouping the labels by charge, $\mathbb D^a$ is spanned by $\{\alpha:\mathrm{chg}(\alpha)=a\}$, $d_a=\dim\mathbb D^a$, and this is
--   $$\mathbb V\cong\bigoplus_a d_a\mathbb V^a\cong\bigoplus_a\big(\mathbb D^a\otimes\mathbb V^a\big),\qquad U_g=\bigoplus_a\big(\mathbb I^a\otimes U^a_g\big).$$
--
--   This is the decomposition that gives every tensor index the form $i=(a,\alpha_a,m_a)$.
--
--   **Formalization Note** The new basis $|a,\alpha_a,m_a\rangle$ is orthonormal ($V$ unitary).
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness is used only for complete reducibility, which a finite-dimensional unitary representation has by orthogonal complements; compact groups with continuous irreps are an instance.
--   - generalization: the irreps of G, labelled by charges a → any catalogue of pairwise inequivalent irreps that covers U; reason: the catalogue of all irreps of G covers every U, so the source's statement is the instance with that catalogue.
--   - reading: 𝕍 ≅ ⊕_a (𝔻^a ⊗ 𝕍^a) in the local basis |a, α_a, m_a⟩ → a unitary change of basis V; reason: the paper's basis of a unitary representation space is orthonormal; the unitary form is the stronger reading.
--   - encoding: degeneracy spaces 𝔻^a → one finite set of labels α with a charge chg(α); reason: 𝔻^a has basis {α : chg(α) = a}; same instances.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eqs. (4)–(5), p.2

import Mathlib
import Definitions.Def_SymTensorNet_IrrepCatalogue

namespace SymTensorNet

universe u v

open Matrix

/-- **Eqs. (4)–(5): the space of one site decomposes into irreps.** Let `U : G → U(N)` be a unitary
matrix representation of a group `G` on `𝕍 = ℂᴺ`, and let `C` be a catalogue of pairwise
inequivalent irreps that covers `U` (every irrep occurring in `U` is equivalent to a member of
`C`). Then there are a finite set `D` of degeneracy labels, a charge `chg α` for each label, and a
unitary change of basis `V` from `ℂᴺ` to `⊕_α 𝕍^{chg α}` in which
`U_g = ⊕_α U^{chg α}_g`, i.e. `U_g = ⊕_a (𝕀ᵃ ⊗ Uᵃ_g)` with `d_a = #{α | chg α = a}`.

arXiv:0907.2994v2, p.2, Eqs. (4)–(5).

**Formalization Note** `G` is a bare group: the paper's compact, completely reducible group is an
instance (unitarity alone gives complete reducibility in finite dimension). The catalogue is part
of the data, and "covers" is the condition that the irreps of `𝕍` are labelled by its charges. -/
theorem eq_4_5 {G : Type u} [Group G] (C : IrrepCatalogue.{u, v} G) {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (hC : Covers C (fun g => (U g : Matrix (Fin N) (Fin N) ℂ))) : ∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (chg : D → C.Charge) (V : Matrix (Fin N) (Σ α : D, Fin (C.dim (chg α))) ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ∀ g : G, Vᴴ * (U g : Matrix (Fin N) (Fin N) ℂ) * V = Matrix.blockDiagonal' (fun α : D => (C.rep (chg α) g : Matrix (Fin (C.dim (chg α))) (Fin (C.dim (chg α))) ℂ)) := by sorry

end SymTensorNet
