-- Prove2me | Theorems.Thm_ValuationSubring_eq_zero_of_valuation_eval2_lt_one
-- name    : ValuationSubring.eq_zero_of_valuation_eval2_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/c43d1e22-3fb7-5dd8-9d9c-7503dd3dec0d
-- title:
--   Algebraically independent residues give no relations in mathfrak m_O
-- statement:
--   Let $k$ and $K$ be fields, $c \colon k \to K$ a ring homomorphism, and $O$ a valuation subring of $K$ such that $c(x) \in O$ for every $x \in k$ (hypothesis `hc`). Let $d$ be a natural number and $g \colon \mathrm{Fin}\,d \to K$ a family of elements of $K$ with $g_i \in O$ for all $i$ (hypothesis `hg`). Equip the residue field $\kappa(O) = O/\mathfrak m_O$ with the $k$-algebra structure coming from the residue map $O \to \kappa(O)$ precomposed with the corestriction of $c$ to $O$, and assume that the family of residues $i \mapsto \overline{g_i} \in \kappa(O)$ (the residues of the elements $g_i$, viewed in $O$ via `hg`) is algebraically independent over $k$ for this structure. Then for every polynomial $Q \in k[X_i : i \in \mathrm{Fin}\,d]$ such that the valuation of $O$ evaluated at $Q^{c}(g_1,\dots,g_d)$ — the image of $Q$ under the evaluation homomorphism with coefficient map $c$ and variables sent to the $g_i$ — is $< 1$, one has $Q = 0$. Equivalently, no non-zero polynomial over $k$ in the $g_i$ lies in the maximal ideal of $O$.
--
--   This is the standard reformulation of 'the residues $\overline{g_1},\dots,\overline{g_d}$ are algebraically independent over $k$' phrased entirely in terms of the valuation of $O$, with no reference to the residue field. It is used in the construction of valuation subrings of a function field with prescribed stalk behaviour, being cited by [`AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one`](thm.html#AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_eq_zero_of_valuation_eval2_lt_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ValuationSubring.eq_zero_of_valuation_eval2_lt_one
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ} (g : Fin d → K) (hg : ∀ i, g i ∈ O)
    (hind :
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩))
    (Q : MvPolynomial (Fin d) k) (hQ : O.valuation (Q.eval₂ c g) < 1) : Q = 0 := by sorry
