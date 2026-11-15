-- Prove2me | Theorems.Thm_Representation_IsIrreducible_invariant_bilinForm_unique_symm_or_alt
-- name    : Representation.IsIrreducible.invariant_bilinForm_unique_symm_or_alt
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T07:11:20.502636+00:00
-- url     : https://prove2.me/theorems/0c4d2a80-d742-4ff8-a490-38c7b7dbb2b7
-- title:
--   Invariant bilinear forms on an irreducible representation are unique up to scalar and symmetric or alternating; normalising maps are similitudes
-- statement:
--   Let $k$ be an algebraically closed field, $V$ a finite-dimensional $k$-vector space and $\rho : G \to \mathrm{GL}(V)$ an irreducible representation of a group $G$. Let $B$ be a nondegenerate bilinear form on $V$ that is $G$-invariant: $B(\rho(g)v, \rho(g)w) = B(v, w)$ for all $g \in G$ and $v, w \in V$. Then:
--
--   1. (**uniqueness**) every $G$-invariant bilinear form $B'$ on $V$ (degenerate or not) is a scalar multiple $B' = c\,B$ of $B$;
--   2. (**symmetric or alternating**) $B$ is either symmetric, $B(v, w) = B(w, v)$ for all $v, w$, or alternating, $B(v, v) = 0$ for all $v$ (so an irreducible self-dual representation is orthogonal or symplectic, and not both unless $\mathrm{char}\,k = 2$);
--   3. (**similitudes**) if a linear automorphism $\Phi$ of $V$ normalises the image of $\rho$, i.e. for every $g \in G$ there is $h \in G$ with $\Phi\,\rho(g) = \rho(h)\,\Phi$, then $\Phi$ is a similitude of $B$: $B(\Phi v, \Phi w) = c\,B(v, w)$ for some $c \neq 0$; and some nonzero scalar multiple $a\,\Phi$ (any $a$ with $a^2 c = 1$) preserves $B$ exactly: $B(a\Phi v, a\Phi w) = B(v, w)$.
--
--   Parts 1 and 2 are the bilinear-form side of Schur's lemma (the Frobenius-Schur dichotomy); part 3 follows by applying part 1 to $B(\Phi\,\cdot, \Phi\,\cdot)$.
--
--   Role: for a geometrically irreducible lisse sheaf on a curve over a finite field ($G$ = the geometric fundamental group, $\Phi$ = a Frobenius element, which normalises it), a geometric self-duality $B$ is unique up to scalar, is orthogonal or symplectic, and becomes an arithmetic self-duality after twisting the sheaf by the character $\mathrm{Frob} \mapsto a$; this is the self-dual twist used in Deligne's theory of weights (Weil II), as presented by Katz.
--
--   **Formalization Note**: the representation is Mathlib's `Representation k G V` with the Mathlib class `[ρ.IsIrreducible]` (the subrepresentation lattice is a simple order, so $V \neq 0$ and the only $G$-stable subspaces are $0$ and $V$). Forms are `LinearMap.BilinForm k V`, nondegeneracy is Mathlib's `LinearMap.BilinForm.Nondegenerate`, and invariance is written elementwise. 'Alternating' is stated as $B(v, v) = 0$ for all $v$, which is stronger than skew-symmetry $B(w, v) = -B(v, w)$ in characteristic 2 (there skew-symmetric forms are symmetric and fall under the first case). The normalising hypothesis on $\Phi$ only asks $\Phi\,\rho(G)\,\Phi^{-1} \subseteq \rho(G)$ elementwise; no automorphism of $G$ is required. Example: the trivial representation on $V = k$ with $B(x, y) = xy$ (symmetric), or the standard representation of $\mathrm{SL}_2(k)$ on $k^2$ with $B = \det$ (alternating).
-- source:
--   I. Schur, "Neue Begründung der Theorie der Gruppencharaktere", Sitzungsber. Preuss. Akad. Wiss. (1905), 406–432 (Schur's lemma); G. Frobenius and I. Schur, "Über die reellen Darstellungen der endlichen Gruppen", Sitzungsber. Preuss. Akad. Wiss. (1906), 186–208 (orthogonal/symplectic dichotomy); used in this form for lisse sheaves (self-dual twist) in N. M. Katz, "L-functions and monodromy: four lectures on Weil II", Adv. Math. 160 (2001), 81–132

import Mathlib

set_option autoImplicit false

theorem Representation.IsIrreducible.invariant_bilinForm_unique_symm_or_alt
    {k G V : Type*} [Field k] [IsAlgClosed k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (hBinv : ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w) :
    (∀ B' : LinearMap.BilinForm k V, (∀ (g : G) (v w : V), B' (ρ g v) (ρ g w) = B' v w) →
      ∃ c : k, B' = c • B) ∧
    ((∀ v w : V, B v w = B w v) ∨ ∀ v : V, B v v = 0) ∧
    ∀ Φ : V ≃ₗ[k] V, (∀ g : G, ∃ h : G, ∀ v : V, Φ (ρ g v) = ρ h (Φ v)) →
      (∃ c : k, c ≠ 0 ∧ ∀ v w : V, B (Φ v) (Φ w) = c * B v w) ∧
      ∃ a : k, a ≠ 0 ∧ ∀ v w : V, B (a • Φ v) (a • Φ w) = B v w := by sorry
