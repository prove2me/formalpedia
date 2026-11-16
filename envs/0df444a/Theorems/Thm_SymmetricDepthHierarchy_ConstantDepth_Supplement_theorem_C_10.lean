-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_C_10
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_C_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:14:35.058136+00:00
-- url     : https://prove2.me/theorems/d8b2a3cd-559b-40e8-9bda-9d3af7c44121
-- title:
--   Theorem C.10 — Stretched-exponential-orbit polynomial support-depth lower bound
-- statement:
--   Let K be any characteristic-zero field. There is one entire family and one infinite set of positive indices for which the following implication holds for every sufficiently large N in that set and every symmetric circuit computing p_N. The same family is outside every fixed polylogarithmic support-depth level. No assertion on all sufficiently large indices outside the chosen set is made.
--
--   $$
--   \exists\eta,\theta>0,\ \exists\mathcal N\subseteq\mathbb N\text{ infinite},\ \exists(p_N)\in\mathrm{symVP}\setminus\mathrm{symVAC}:\quad \operatorname{maxOrb}(C)\le2^{N^\eta}\ \Longrightarrow\ \operatorname{supportDepth}(C)\ge N^\theta.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 46 (PDF p. 49), Theorem C.10; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_C_10 (K : Type) [Field K] [CharZero K] :
    ∃ η θ : ℝ, 0 < η ∧ 0 < θ ∧ ∃ S : Set ℕ, S.Infinite ∧
      ∃ p : Family K, p ∈ symVP K ∧ p ∉ symVAC K ∧
        ∃ N₀ : ℕ, ∀ N ∈ S, 1 ≤ N → N₀ ≤ N →
          ∀ {V : Type} [Fintype V] (C : Circuit K N V),
            C.WellFormed → C.MatrixSymmetric → C.Computes (p N) →
            (C.maxOrb : ℝ) ≤ Real.rpow 2 (Real.rpow N η) →
            Real.rpow N θ ≤ C.supportDepth := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
