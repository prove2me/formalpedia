-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_oneCallCommutant
-- name    : QAlgorithms.Papers.Independent.Support50.P24.oneCallCommutant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:57:16.263378+00:00
-- url     : https://prove2.me/theorems/82d4e434-f52e-49cd-89fe-9061b9c7e35a
-- title:
--   One-call commutant has four sector generators
-- statement:
--   Let $d\ge1$ and let $C$ be any complex matrix on four $d$-dimensional wires, grouped into two pairs. Put $\Pi_+=(I+S)/2$ and $\Pi_-=(I-S)/2$, where $S$ swaps the two factors of a pair. Then
--
--   $$[C,V^{\otimes2}\otimes W^{\otimes2}]=0\quad\text{for all }V,W\in\mathrm{SU}(d)
--   \quad\Longleftrightarrow\quad
--   C=\sum_{\mu,\nu\in\{+,-\}}c_{\mu\nu}\Pi_\mu\otimes\Pi_\nu$$
--
--   for some complex coefficients $c_{\mu\nu}$. The two group actions are independent. No positivity or causal normalization is imposed on $C$. At $d=1$ the antisymmetric sector vanishes, so the coefficients need not be unique. This characterizes the invariant search space in the one-call example.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 3, Unnumbered example, Eq.(12): one-call four-sector reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF p.3, Eq.(12): arbitrary matrices in the independent tensor-square commutant
are precisely linear combinations of the four physical sectors. At d=1 no uniqueness is claimed. -/
theorem oneCallCommutant (d : ℕ) (hd : 0 < d)
    (C : QAlgorithms.Papers.Independent.Next46.P24.CombMatrix d) :
    QAlgorithms.Papers.Independent.Next46.P24.InversionCovariant C ↔
      ∃ coefficient : Bool → Bool → ℂ,
        C = ∑ b : Bool, ∑ c : Bool, coefficient b c •
          QAlgorithms.Papers.Independent.Next46.P24.inversionSector d b c := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
