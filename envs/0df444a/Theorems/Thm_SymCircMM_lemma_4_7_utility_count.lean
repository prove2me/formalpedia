-- Prove2me | Theorems.Thm_SymCircMM_lemma_4_7_utility_count
-- name    : SymCircMM.lemma_4_7_utility_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:43.659555+00:00
-- url     : https://prove2.me/theorems/fce166a5-28d2-4108-8253-66a635b72dcb
-- title:
--   Lemma 4.7 — $\sum_{O\in M/G}\mathrm{util}(O)\ge n^2N$
-- statement:
--   Let $M$ be the multiplicative layer of a rigid bilinear $G$-symmetric circuit for $\mathrm{MM}_n$ (Proposition 4.2): each gate $g\in M$ computes $L(X)\,R(Y)$ with $L$ a linear form in the $A$-variables and $R$ a linear form in the $B$-variables, and $G$ acts on $M$, the image $\hat\sigma(g)$ computing $\sigma\cdot g$. Assume $\mathrm{char}(F)\nmid|G|$ and that every output $C_{a,b}$ is an $F$-linear combination of the functions computed by the gates of $M$. Let $V_1,\dots,V_r$ be pairwise inequivalent irreducible constituents of the permutation representation, $d_i=\dim V_i$, $N=\sum_id_i$, and let $\mathrm{util}$ be the utility of Definition 4.5. Then
--
--   $$\sum_{O\in M/G}\mathrm{util}(O)\ \ge\ n^2N.$$
--
--   Together with Lemma 4.8 this bounds the number of product gates from below by $n^2N$.
--
--   **Formalization Note** $M$ is any finite set with a $G$-action and gate data $L_m$, $R_m$ satisfying $L_{\sigma\cdot m}=L_m\circ(X\mapsto X\circ\sigma)$ and $R_{\sigma\cdot m}=R_m\circ(Y\mapsto\sigma\cdot Y)$; the rigid circuit of Proposition 4.2 gives such data. The constituents are a family $W$ of pairwise inequivalent irreducible subrepresentations with partners $W'_s\simeq W_s^*$ (the $V_{i^*}$), and $\mathrm{util}(O)$ is the utility of a representative of $O$.
--
--   Differences from the source:
--
--   - generalization: the multiplicative layer M of the rigid bilinear G-symmetric circuit C′, with features (i)–(iii) (PDF pp.10–11) → any finite G-set M with linear forms L m on A and R m on B, the gate m computing L m(X)·R m(Y), and L (σ•m) = L m ∘ (X ↦ X∘σ), R (σ•m) = R m ∘ (Y ↦ σ·Y); reason: the rigid circuit C′ of Proposition 4.2 gives such data (σ̂ acts on M and maps the A- and B-inputs of m to those of σ̂m); the proof uses only these features
--   - encoding: functions A × B → F → curried functions Matrix ι ι F → Matrix ι ι F → F (restrictions as functions on the product of the subspaces A_i × B_i); reason: Lean convention; the same functions
--   - generalization: N = ∑_i dim V_i over the pairwise inequivalent constituents V_1, …, V_r of a decomposition λ_1V_1 ⊕ ⋯ ⊕ λ_rV_r of the permutation representation → ∑_s finrank W_s over any family W of pairwise inequivalent irreducible subrepresentations of the permutation representation; reason: one copy of each V_i inside the decomposition is such a family and gives the paper's N; every such family has sum at most N
--   - reading: U_{i*}, the isotypic component of the constituent V_{i*} ≃ V_i^* (the involution i ↦ i*, PDF p.12) → the isotypic component of an irreducible subrepresentation W′ with W′ ≃ W^* (W = V_i); reason: i* is defined by V_{i*} ≃ V_i^*, and the isotypic component depends only on the equivalence class
--   - encoding: util(O) for an orbit O ∈ M/G → util of the representative Quotient.out O; reason: util is constant on orbits (PDF p.14)
--   - encoding: char(F) ∤ |G| → (Nat.card G : F) ≠ 0; reason: a prime p divides m iff (m : F) = 0 in characteristic p, and (m : F) ≠ 0 for every m ≥ 1 in characteristic 0
--   - encoding: (ii): each output C_{a,b} is an F-linear combination of the polynomials computed by the gates of M → hout: each mmForm a b lies in the span of the gate functions; reason: the same condition on functions
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Lemma 4.7, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SymCircMM_util

open scoped Classical

set_option autoImplicit false

namespace SymCircMM

/-- **Lemma 4.7** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.13 (PDF p.14)): "∑_{O∈M/G} util(O) ≥ n²N." Here `N = ∑_i d_i`,
`d_i = dim V_i`, and every output `C_{a,b}` is an `F`-linear combination of the gates of `M`
(feature (ii)); `char F ∤ |G|` (§4.2).

**Formalization Note.** The multiplicative layer `M` of the bilinear rigid `G`-symmetric circuit is a finite
`G`-set (rigidity makes the extension `σ̂` unique, feature (iii)); gate `m` computes `L m (X) · R m (Y)`
with `L m` an `A`-linear and `R m` a `B`-linear form (feature (i)), and `σ̂` maps the `A`-input of `m`
to that of `σ̂ m`: `L (σ • m) = L m ∘ (X ↦ X ∘ σ)`, likewise for `R` (the action (2) on matrices). The constituents `V₁, …, V_r` are a family `W` of pairwise inequivalent irreducible
subrepresentations of the permutation representation, and `W' s ≃ (W s)^*` plays `V_{i*}`, so `util`
(`Definition 4.5`) restricts to `A_s × B_s` with `B_s` built from the isotypic component of `W' s`. `util(O)` is the utility of a representative of `O`
(it is constant on orbits, p.13 (PDF p.14)); `n = card ι`. -/
theorem lemma_4_7_utility_count {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (Equiv.Perm ι)) (hG : (Nat.card G : F) ≠ 0)
    {M : Type} [Fintype M] [MulAction G M] (L R : M → Module.Dual F (Matrix ι ι F))
    (hL : ∀ (σ : G) (m : M), L (σ • m) = (L m).comp (colPerm (σ : Equiv.Perm ι)))
    (hR : ∀ (σ : G) (m : M), R (σ • m) = (R m).comp (rowPerm (σ : Equiv.Perm ι)))
    (hout : ∀ a b, mmForm a b ∈ Submodule.span F (Set.range (gateForm L R)))
    {r : ℕ} (W W' : Fin r → Subrepresentation (permRep F G))
    (hW : ∀ s, (W s).toRepresentation.IsIrreducible)
    (hWW : ∀ s t, s ≠ t → IsEmpty ((W s).toRepresentation.Equiv (W t).toRepresentation))
    (hW' : ∀ s, Nonempty ((W' s).toRepresentation.Equiv (W s).toRepresentation.dual)) :
    Fintype.card ι ^ 2 * ∑ s, Module.finrank F (W s).toSubmodule ≤
      ∑ O : MulAction.orbitRel.Quotient G M, util W W' L R (Quotient.out O) := by sorry

end SymCircMM
