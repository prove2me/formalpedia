-- Prove2me | Theorems.Thm_PadicComplex_forall_smul_eq_self_iff_mem_closure
-- name    : PadicComplex.forall_smul_eq_self_iff_mem_closure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/b2aeecb8-6177-5f6e-8e73-838e6bb4cdf4
-- title:
--   Ax–Sen–Tate: ℂₚ-invariants are the closure of K
-- statement:
--   Let $p$ be a prime, let `PadicAlgCl p` denote the algebraic closure $\overline{\mathbb{Q}}_p$ of $\mathbb{Q}_p$ and let $\mathbb{C}_p$ (`ℂ_[p]`) be its completion, carrying the induced action of the automorphism group $\overline{\mathbb{Q}}_p \simeq_{\mathrm{alg}[\mathbb{Q}_p]} \overline{\mathbb{Q}}_p$ by scalar multiplication. Let $K$ be an intermediate field of the extension $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$, and let $x \in \mathbb{C}_p$. The assertion is an equivalence of two conditions on $x$: first, that $\sigma \bullet x = x$ for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ lying in the fixing subgroup of $K$, i.e. for every $\sigma$ with $\sigma k = k$ for all $k \in K$; second, that $x$ belongs to the topological closure in $\mathbb{C}_p$ of the range of the map sending $k \in K$ to the image of $k$ in $\mathbb{C}_p$, that is, to the closure of $K$ inside $\mathbb{C}_p$. No finiteness, closedness or completeness hypothesis is imposed on $K$.
--
--   This is the theorem of Tate, in the generality of Ax and Sen: the $\mathbb{C}_p$-invariants of the group of automorphisms of $\overline{\mathbb{Q}}_p$ fixing $K$ form exactly the closure of $K$; for $K/\mathbb{Q}_p$ finite this reads $\mathbb{C}_p^{G_K} = K$. It is the basic input to the Galois theory of $\mathbb{C}_p$ used in the Hodge–Tate analysis of $p$-adic representations, and is cited here in the study of the cyclotomic character twists of continuous cocycles valued in $\mathbb{C}_p$ and in the Cartier-duality analysis of Tate modules of $p$-divisible groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicComplex_forall_smul_eq_self_iff_mem_closure.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicComplex.forall_smul_eq_self_iff_mem_closure
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → σ • x = x) ↔
      x ∈ closure (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) := by sorry
