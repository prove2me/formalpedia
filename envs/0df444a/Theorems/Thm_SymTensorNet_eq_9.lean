-- Prove2me | Theorems.Thm_SymTensorNet_eq_9
-- name    : SymTensorNet.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:24.647727+00:00
-- url     : https://prove2.me/theorems/c14cf757-eeee-41dc-99e5-792fd4a498af
-- title:
--   Eq. (9) — the tensor product of two irreps decomposes into irreps by Clebsch–Gordan isometries
-- statement:
--   Let $\{U^a\}$ be a catalogue of pairwise inequivalent irreps of a group $G$ such that
--   1. it contains the trivial irrep: a charge $0$ with $\dim 0=1$ and $U^0_g=1$;
--   2. it covers every tensor product $U^a\otimes U^b$;
--   3. it covers every complex conjugate $\overline{U^a}$.
--
--   Then the catalogue carries fusion data: for every pair $(a,b)$ there are finitely many channels $\kappa$ with output charges $c=\mathrm{out}(\kappa)$ and isometries $\iota_\kappa=(Q^{abc})_{m_an_bo_c}$ that intertwine $U^a\otimes U^b$ with $U^c$, are orthonormal and are complete, so that
--   $$\mathbb V^a\otimes\mathbb V^b\cong\bigoplus_cN^c_{ab}\mathbb V^c$$
--   with $N^c_{ab}$ the number of channels with output $c$ and $Q^{abc}$ the change of basis from the product basis $|a,m_a\rangle\otimes|b,n_b\rangle$ to the coupled basis $|c,o_c\rangle$. The catalogue also carries conjugation data: every $\overline{U^a}$ is unitarily equivalent to a catalogue irrep $U^{\bar a}$.
--
--   This shows that the fusion data assumed by Eqs. (10)–(15) exists.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness is used only for complete reducibility, which finite-dimensional unitary representations have; compact groups with continuous irreps are an instance.
--   - generalization: G multiplicity free, N^c_ab ≤ 1 → any finite number of channels per output charge; reason: footnote [10]; the multiplicity-free case is the one with distinct outputs on each pair.
--   - generalization: the irreps of G → any catalogue containing the trivial irrep and covering tensor products and conjugates; reason: the catalogue of all irreps of G has these properties, so the source's case is an instance.
--   - generalization: Eq. (9) alone → Eq. (9) and conjugation data (each conjugate irrep is unitarily equivalent to a catalogue irrep); reason: incoming legs carry the conjugate representation (Eq. (7)); dropping the second conclusion gives Eq. (9).
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (9) and the change of basis (Q^{abc}), p.2; footnote [10], p.4

import Mathlib
import Definitions.Def_SymTensorNet_FusionData

namespace SymTensorNet

universe u v

open Matrix
open scoped Kronecker

/-- **Eq. (9): fusion data exists.** Let `C` be a catalogue of pairwise inequivalent irreps of a
group `G` that contains the trivial irrep (a charge `0` with `dim 0 = 1`, `U⁰_g = 1`), covers every
tensor product `Uᵃ ⊗ Uᵇ`, and covers every conjugate `conj(Uᵃ)`. Then `C` extends to fusion data:
for every pair `(a, b)` there are finitely many channels with Clebsch–Gordan isometries that
intertwine, are orthonormal and complete, decomposing `𝕍ᵃ ⊗ 𝕍ᵇ ≅ ⊕_c N^c_{ab} 𝕍^c`; and every
conjugate irrep is unitarily equivalent to a catalogue irrep `U^ā` (conjugation data).

arXiv:0907.2994v2, p.2, Eq. (9) and the change of basis `(Q^{abc})_{m_a n_b o_c}`; footnote [10],
p.4.

**Formalization Note** `G` is a bare group, and multiplicity freeness is not assumed: the
channels of `(a, b)` with output `c` number `N^c_{ab}`. -/
theorem eq_9 {G : Type u} [Group G] (C : IrrepCatalogue.{u, v} G) (h0 : ∃ z : C.Charge, ∃ hz : C.dim z = 1, ∀ g : G, (C.rep z g : Matrix (Fin (C.dim z)) (Fin (C.dim z)) ℂ) = 1) (hprod : ∀ a b : C.Charge, Covers C (fun g : G => (C.rep a g : Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ) ⊗ₖ (C.rep b g : Matrix (Fin (C.dim b)) (Fin (C.dim b)) ℂ))) (hconj : ∀ a : C.Charge, Covers C (fun g : G => (C.rep a g : Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ).map star)) : (∃ F : FusionData.{u, v} G, F.toIrrepCatalogue = C) ∧ Nonempty (ConjData C) := by sorry

end SymTensorNet
