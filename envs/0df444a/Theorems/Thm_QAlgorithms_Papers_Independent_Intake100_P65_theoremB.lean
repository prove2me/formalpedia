-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_theoremB
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.theoremB
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:12:29.63036+00:00
-- url     : https://prove2.me/theorems/6e7fc6a7-eb89-4e96-8bfb-9d0b30ef048e
-- title:
--   Strict cellularity of the cyclotomic algebra
-- statement:
--   Under the hypotheses of Theorem A, $A=W_{r,n}(u;\Omega)$ has a cell datum. More precisely, there are a partially ordered label set $\Lambda$, finite sets $T(\lambda)$, an $R$-basis $C_{st}^\lambda$ of $A$, and an $R$-linear involutive anti-isomorphism $*$ such that
--
--   $$(C_{st}^\lambda)^*=C_{ts}^\lambda,\qquad aC_{st}^\lambda\equiv\sum_{v\in T(\lambda)}r_{sv}(a)C_{vt}^\lambda\pmod{A^{>\lambda}}.$$
--
--   Here $A^{>\lambda}$ is the span of basis elements with strictly higher labels, and the coefficients $r_{sv}(a)\in R$ are independent of $t$. This is strict cellularity in the sense of Definition 6.2, providing the cell-module framework.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 2, Theorem B

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Theorem B, PDF p.2, with the strict cell datum of Definition 6.2, p.41.
The anti-involution swaps basis indices exactly; multiplication coefficients
are chosen before the column index. No field or genericity is assumed. -/
theorem theoremB (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (u : Fin r → R) (ha : RootAdmissible omega u) :
    ∃ (L : Type u) (ord : PartialOrder L) (T : L → Type u)
      (fin : ∀ l, Fintype (T l))
      (b : Module.Basis (CellIndex L T) R (Cyclotomic R omega .degenerate r u n))
      (star : Cyclotomic R omega .degenerate r u n →ₗ[R]
        Cyclotomic R omega .degenerate r u n),
      letI : PartialOrder L := ord
      letI : ∀ l, Fintype (T l) := fin
      Function.Involutive star ∧
      (∀ a c, star (a*c) = star c * star a) ∧
      (∀ l (s t : T l), star (b ⟨l, (s,t)⟩) = b ⟨l, (t,s)⟩) ∧
      (∀ l (s : T l) a, ∃ coeff : T l → R, ∀ t : T l,
        a * b ⟨l, (s,t)⟩ - ∑ z : T l, coeff z • b ⟨l, (z,t)⟩ ∈
          higherCellSpan (R := R) (fun i => b i) l) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
