-- Prove2me | Theorems.Thm_SymTensorNet_tree_basis
-- name    : SymTensorNet.tree_basis
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:21:23.051139+00:00
-- url     : https://prove2.me/theorems/d07dd993-78cb-44f8-8f8a-bc27fd61df58
-- title:
--   A trivalent tree labels an orthonormal basis of intertwiners between tensor products of incoming and outgoing irreps
-- statement:
--   Let $G$ be a group with fusion data for a catalogue of irreps. Let $\tau$ be a fusion tree whose leaves are all the legs $s\in S$, each exactly once, let $x_s$ be the charge of leg $s$, and let $W(\tau,\ell)$ be the fusion-tree maps, one for each labelling $\ell$ of the inner branches by intermediate charges $e_1,\dots,e_{t'}$ (and channels), with top charge $c_\ell$. Then:
--   1. **(intertwiners)** $\big(\bigotimes_sU^{x_s}_g\big)\,W(\tau,\ell)=W(\tau,\ell)\,U^{c_\ell}_g$ for all $g\in G$;
--   2. **(orthonormal)** $\sum_m\overline{W(\tau,\ell)(m,o)}\,W(\tau,\ell')(m,o')=1$ if $\ell=\ell'$ and $o=o'$, and $=0$ otherwise;
--   3. **(complete)** $\sum_\ell\sum_oW(\tau,\ell)(m,o)\,\overline{W(\tau,\ell)(m',o)}=\delta_{mm'}$;
--   4. **(basis)** for every charge $c$, every intertwiner $X$ from $U^c$ into $\bigotimes_sU^{x_s}$ (i.e. $(\bigotimes_sU^{x_s}_g)X=XU^c_g$ for all $g$) can be written as
--   $$X=\sum_{\ell:\,c_\ell=c}\lambda_\ell\,W(\tau,\ell)$$
--   for exactly one family of coefficients $\lambda_\ell$;
--   5. **(incoming and outgoing irreps)** for any directions (outgoing/incoming) of the legs, any conjugation data ($\bar a$ and unitaries $J^a$ with $J^a\,\overline{U^a_g}=U^{\bar a}_gJ^a$), any root leg $r$, any tree $\tau'$ in which every leg other than $r$ occurs exactly once and $r$ does not occur, and any leg charges $a$: the structural tensors $Q(a,\ell)$ of $\tau'$ (incoming legs and an outgoing root enter the tree through $J$) for the labellings $\ell$ whose top charge is the root charge are invariant, and every tensor $X$ on $\bigotimes_s\mathbb V^{a_s}$ invariant under $U^{a_s}_g$ on outgoing legs and $\overline{U^{a_s}_g}$ on incoming legs (Eq. (7)) — that is, every intertwiner between the tensor product of the incoming irreps and that of the outgoing irreps — can be written as $X=\sum_\ell\lambda_\ell\,Q(a,\ell)$ for exactly one family $\lambda_\ell$.
--
--   So the labellings of the tree by intermediate charges label a basis of the space of intertwining operators between the tensor products of incoming and outgoing irreps.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness only supplies complete reducibility, which unitarity gives; compact groups are an instance.
--   - generalization: G multiplicity free, inner branches labelled by charges e_k → labelled by channels; reason: footnote [10]; with multiplicity freeness a channel is determined by its charge.
--   - encoding: an intertwining operator between the tensor products of incoming and outgoing irreps → a tensor with one leg per irrep, invariant under U_g on outgoing and conj(U_g) on incoming legs (clause 5), with the tree rooted at a leg r and incoming legs entering it through a conjugation unitary J^a; reason: Hom(⊗ incoming, ⊗ outgoing) is identified with the invariant tensors exactly as in Eq. (7); clauses 1–4 add the case of one irrep into a product, with orthonormality and completeness.
--   - generalization: trivalent trees → trees that may also have trivial leaves (charge 0); reason: the trivial leaf is needed for one-leg tensors; trees without trivial leaves are an instance.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, paragraph after Eq. (15) ("Here e1, e2, ..., et′ are intermediate charges that decorate the inner branches of a trivalent tree used to label a basis in the space of intertwining operators"), p.3

import Mathlib
import Definitions.Def_SymTensorNet_StructuralTensor

namespace SymTensorNet

universe u v w

open Matrix

/-- **A trivalent tree labels a basis of intertwiners.** Let `τ` be a fusion tree whose leaves are
all the legs `S`, each exactly once, and let `x s` be the charge of leg `s`. The fusion-tree maps
`W(τ, ℓ)` (one for each labelling `ℓ` of the inner branches by intermediate charges and channels)
satisfy:
1. (intertwiners) `(⊗_s U^{x s}_g) W(τ, ℓ) = W(τ, ℓ) U^{top ℓ}_g` for all `g`;
2. (orthonormal) `Σ_m conj(W(τ, ℓ)(m, o)) W(τ, ℓ′)(m, o′) = 1` if `ℓ = ℓ′` and `o = o′`, and `0`
   otherwise;
3. (complete) `Σ_ℓ Σ_o W(τ, ℓ)(m, o) conj(W(τ, ℓ)(m′, o)) = δ_{m m′}`;
4. (basis) for every charge `c`, every intertwiner `X` from `U^c` to `⊗_s U^{x s}` is
   `Σ_ℓ λ_ℓ W(τ, ℓ)` over the labellings with top charge `c`, for exactly one family `λ`;
5. (incoming and outgoing irreps) for any directions of the legs, any conjugation data `K`, any
   root leg `r`, any tree `τ'` valid for `r` and any leg charges `a`, the structural tensors
   `Q(a, ℓ)` (`structQ`, built from `τ'` with incoming legs entering through `conj(J)`) for the
   admissible labellings `ℓ` are invariant, and every tensor on `⊗_s 𝕍^{a_s}` invariant under
   `U^{a_s}` on outgoing and `conj(U^{a_s})` on incoming legs, i.e. every intertwiner between the
   tensor product of the incoming irreps and that of the outgoing irreps, is `Σ_ℓ λ_ℓ Q(a, ℓ)` for
   exactly one family `λ`.

arXiv:0907.2994v2, p.3, after Eq. (15): "e₁, e₂, …, e_{t′} are intermediate charges that decorate
the inner branches of a trivalent tree used to label a basis in the space of intertwining operators
between the tensor products of incoming and outgoing irreps".

**Formalization Note** Clauses 1–4 are the intertwiners from one irrep `U^c` into the tensor product
of the leaf irreps. Clause 5 is the paper's general case: an intertwiner from the tensor product of
the incoming irreps to that of the outgoing irreps is encoded as a tensor with one leg per irrep,
invariant under Eq. (7)'s action; the tree is rooted at a leg `r`, and incoming legs (and an
outgoing root) enter the tree through the conjugation unitaries `J` of `K`. `G` is a bare group; channels replace multiplicity-free fusion (footnote [10]). -/
theorem tree_basis {G : Type u} [Group G] (F : FusionData.{u, v} G) {S : Type w} [Fintype S] [DecidableEq S] (x : S → F.Charge) (τ : Tree S) (hnd : τ.leaves.Nodup) (hall : ∀ s, s ∈ τ.leaves) : (∀ (g : G) (ℓ : Lab F x τ) (m : (s : S) → Fin (F.dim (x s))) (o : Fin (F.dim (top F x τ ℓ))), ∑ n : (s : S) → Fin (F.dim (x s)), (∏ s, (F.rep (x s) g : Matrix (Fin (F.dim (x s))) (Fin (F.dim (x s))) ℂ) (m s) (n s)) * treeW F x τ ℓ n o = ∑ o' : Fin (F.dim (top F x τ ℓ)), treeW F x τ ℓ m o' * (F.rep (top F x τ ℓ) g : Matrix (Fin (F.dim (top F x τ ℓ))) (Fin (F.dim (top F x τ ℓ))) ℂ) o' o) ∧ (∀ (ℓ ℓ' : Lab F x τ) (o : Fin (F.dim (top F x τ ℓ))) (o' : Fin (F.dim (top F x τ ℓ'))), ∑ m : (s : S) → Fin (F.dim (x s)), star (treeW F x τ ℓ m o) * treeW F x τ ℓ' m o' = if ℓ = ℓ' ∧ (o : ℕ) = (o' : ℕ) then 1 else 0) ∧ (∀ m m' : (s : S) → Fin (F.dim (x s)), ∑ ℓ : Lab F x τ, ∑ o : Fin (F.dim (top F x τ ℓ)), treeW F x τ ℓ m o * star (treeW F x τ ℓ m' o) = if m = m' then 1 else 0) ∧ (∀ (c : F.Charge) (X : ((s : S) → Fin (F.dim (x s))) → Fin (F.dim c) → ℂ), (∀ (g : G) (m : (s : S) → Fin (F.dim (x s))) (o : Fin (F.dim c)), ∑ n : (s : S) → Fin (F.dim (x s)), (∏ s, (F.rep (x s) g : Matrix (Fin (F.dim (x s))) (Fin (F.dim (x s))) ℂ) (m s) (n s)) * X n o = ∑ o' : Fin (F.dim c), X m o' * (F.rep c g : Matrix (Fin (F.dim c)) (Fin (F.dim c)) ℂ) o' o) → ∃! lam : {ℓ : Lab F x τ // top F x τ ℓ = c} → ℂ, ∀ (m : (s : S) → Fin (F.dim (x s))) (o : Fin (F.dim c)), X m o = ∑ ℓ : {ℓ : Lab F x τ // top F x τ ℓ = c}, lam ℓ * treeW F x τ ℓ.1 m (Fin.cast (congrArg F.dim ℓ.2.symm) o)) ∧ (∀ (K : ConjData F.toIrrepCatalogue) (dir : S → Dir) (r : S) (τ' : Tree S), IsValidTree τ' r → ∀ a : S → F.Charge, (∀ (ℓ : AdmLab F K dir τ' r a) (g : G) (m : (s : S) → Fin (F.dim (a s))), ∑ n : (s : S) → Fin (F.dim (a s)), (∏ s, legRep F.toIrrepCatalogue (dir s) (a s) g (m s) (n s)) * structQ F K dir τ' r a ℓ n = structQ F K dir τ' r a ℓ m) ∧ (∀ X : ((s : S) → Fin (F.dim (a s))) → ℂ, (∀ (g : G) (m : (s : S) → Fin (F.dim (a s))), ∑ n : (s : S) → Fin (F.dim (a s)), (∏ s, legRep F.toIrrepCatalogue (dir s) (a s) g (m s) (n s)) * X n = X m) → ∃! lam : AdmLab F K dir τ' r a → ℂ, ∀ m : (s : S) → Fin (F.dim (a s)), X m = ∑ ℓ : AdmLab F K dir τ' r a, lam ℓ * structQ F K dir τ' r a ℓ m)) := by sorry

end SymTensorNet
