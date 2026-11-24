-- Prove2me | Theorems.Thm_SameStatePairs_permutation_gauge
-- name    : SameStatePairs.permutation_gauge
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T21:06:44.203448+00:00
-- url     : https://prove2.me/theorems/c946f817-46ba-4f11-b277-9dfa90c9d210
-- title:
--   Proposition 4: the permutation gauge
-- statement:
--   Let $A\in\mathbb{R}^{n\times d}$ have full column rank, let $P\in S_d$ be a permutation identified with its permutation matrix, and let $B=AP$. Observations $X=APZ+N$ depend on $A$ and $P$ only through $B$:
--
--   1. $A(Pz)=Bz$ for every $z\in\mathbb{R}^d$.
--   2. For every $P_0\in S_d$, the transformation $(A,P)\mapsto(AP_0,P_0^{-1}P)$ leaves $B$ unchanged: $(AP_0)(P_0^{-1}P)=AP$.
--   3. With $A$ free, the decomposition $B=A'P'$ with $A'\in\mathbb{R}^{n\times d}$ and $P'\in S_d$ has exactly $d!$ solutions $(A',P')$.
--   4. Every solution is $(AP_0,P_0^{-1}P)$ for some $P_0\in S_d$.
--
--   So an absolute permutation is not identifiable from the data.
--
--   **Formalization Note** "Identified with its permutation matrix" uses Mathlib's `Equiv.Perm.permMatrix`. The informal conclusion "an absolute permutation is not identifiable" is the content of items 2–4.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 4.4, Proposition 4, p. 8; proof in Appendix A.5, p. 13

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem permutation_gauge {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (hA : A.rank = d)
    (σ : Equiv.Perm (Fin d)) :
    (∀ z : Fin d → ℝ, A *ᵥ (σ.permMatrix ℝ *ᵥ z) = (A * σ.permMatrix ℝ) *ᵥ z) ∧
    (∀ σ₀ : Equiv.Perm (Fin d),
      (A * σ₀.permMatrix ℝ) * ((σ₀.permMatrix ℝ)⁻¹ * σ.permMatrix ℝ) = A * σ.permMatrix ℝ) ∧
    {AP : Matrix (Fin n) (Fin d) ℝ × Equiv.Perm (Fin d) |
      AP.1 * AP.2.permMatrix ℝ = A * σ.permMatrix ℝ}.ncard = d.factorial ∧
    (∀ AP : Matrix (Fin n) (Fin d) ℝ × Equiv.Perm (Fin d),
      AP.1 * AP.2.permMatrix ℝ = A * σ.permMatrix ℝ →
      ∃ σ₀ : Equiv.Perm (Fin d), AP.1 = A * σ₀.permMatrix ℝ ∧
        AP.2.permMatrix ℝ = (σ₀.permMatrix ℝ)⁻¹ * σ.permMatrix ℝ) := by sorry

end SameStatePairs
