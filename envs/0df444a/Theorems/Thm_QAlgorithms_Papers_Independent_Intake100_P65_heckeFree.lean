-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_heckeFree
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.heckeFree
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:24:44.910738+00:00
-- url     : https://prove2.me/theorems/ab1ee6dd-d6a4-44a2-b89d-7d86a8d41efd
-- title:
--   Freeness and rank of the degenerate cyclotomic Hecke algebra
-- statement:
--   Let $R$ be a commutative unital ring in which $2$ is invertible, let $n,r\ge1$, and let $u\in R^r$. The degenerate cyclotomic Hecke algebra $H_{r,n}(u)$ of the presentation on PDF p.10 is free as an $R$-module with a basis of cardinality
--
--   $$r^n n!.$$
--
--   No genericity, field, or $\Omega$ hypothesis is required.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 40, Theorem 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Theorem 6.1, PDF p.40: the degenerate cyclotomic Hecke algebra is free
of rank r^n n! over the specified ground ring. The named PBW basis in its
proof is not required to express this numbered freeness statement. -/
theorem heckeFree (R : Type u) [CommRing R] [Invertible (2 : R)]
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (roots : Fin r → R) :
    Nonempty (Module.Basis (Fin (r^n * n.factorial)) R
      (CyclotomicHeckeAlgebra R n r roots)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
