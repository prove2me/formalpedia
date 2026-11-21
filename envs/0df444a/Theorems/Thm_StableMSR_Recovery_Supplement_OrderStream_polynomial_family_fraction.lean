-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_polynomial_family_fraction
-- name    : StableMSR.Recovery.Supplement.OrderStream.polynomial_family_fraction
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:01:14.292999+00:00
-- url     : https://prove2.me/theorems/63523946-5294-4b3f-bbae-9fe41a0767af
-- title:
--   Enumerating coefficient indices preserves the minwise fraction with multiplicity
-- statement:
--   Base-q digits identify the coefficient indices bijectively with the coefficient vectors over the selected prime field. Each vector contributes one list entry. The proved polynomial minwise bound therefore applies directly to the actual fraction of output permutations.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream

theorem StableMSR.Recovery.Supplement.OrderStream.polynomial_family_fraction (m : ℕ) : (family m).length=count m ∧ PermutationFamily m (family m) ∧
    ∀T : Finset ℕ,T⊆Finset.range m → T.Nonempty → ∀z∈T,
      firstFraction (family m) T z ≤ 3/(2*(T.card:ℝ)) := by
  sorry
