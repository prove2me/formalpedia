-- Prove2me | Theorems.Thm_Smooth4Algebra_unsaturated_corner_budget
-- name    : Smooth4Algebra.unsaturated_corner_budget
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:38:59.59988+00:00
-- url     : https://prove2.me/theorems/f6cc0221-29eb-4e8a-9649-8856b2954f2a
-- title:
--   Two-corner homology bound with incoming and outgoing ranks
-- statement:
--   Let $d:V\to V$ be square-zero in finite dimension over a field. Let $E$ and $F$ be two split, distinct linear blocks with inclusions and projections that are identities on their own block and zero on the other. Assume the outgoing/incoming ranks of $E$ are at most $c_-$ and $r_+$, and those of $F$ are at most $r_-$ and $c_+$. Then
--
--   $$\dim H(V,d)\ge\max(0,\dim E-r_+-c_-)+\max(0,\dim F-r_--c_+).$$
--
--   This is the linear-algebra form of the unsaturated opposite-corner bound. In a bifiltered application, the corner-incidence argument must separately establish the four stated rank bounds.
-- source:
--   Newly authored from cycle21_corner_budget_independent.md, §1 joint cycle-subspace argument; SHA-256 89aa667aee6440fe989e7664eec02f5a7a60010d1d86a77dd094bdf95ba8bdba. This is a new Lean formalization, not an existing source-project theorem split.

import Definitions.Def_Smooth4AlgebraHomology
set_option autoImplicit false

theorem Smooth4Algebra.unsaturated_corner_budget
    {K V E F : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F]
    (d : V →ₗ[K] V) (h_square : d.comp d = 0)
    (incE : E →ₗ[K] V) (incF : F →ₗ[K] V)
    (projE : V →ₗ[K] E) (projF : V →ₗ[K] F)
    (hE : projE.comp incE = LinearMap.id)
    (hF : projF.comp incF = LinearMap.id)
    (hEF : projE.comp incF = 0) (hFE : projF.comp incE = 0)
    (rPlus rMinus cPlus cMinus : ℕ)
    (hEout : Module.finrank K (LinearMap.range (d.comp incE)) ≤ cMinus)
    (hEin : Module.finrank K (LinearMap.range (projE.comp d)) ≤ rPlus)
    (hFout : Module.finrank K (LinearMap.range (d.comp incF)) ≤ rMinus)
    (hFin : Module.finrank K (LinearMap.range (projF.comp d)) ≤ cPlus) :
    (Module.finrank K E - rPlus - cMinus) +
      (Module.finrank K F - rMinus - cPlus) ≤
        Module.finrank K (Smooth4Algebra.Homology d) := by sorry
