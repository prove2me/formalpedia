-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_product_lower_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P56.product_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:17:01.767203+00:00
-- url     : https://prove2.me/theorems/9feb1d52-7ab1-445a-8ac4-4935dc8d1afc
-- title:
--   Section III, Eq.(13): product lower bound
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. For every integer $n\ge1$, let $C^{(n)}$ be the supremum of $I(V;B^n)-I(V;E^n)$ over every finite auxiliary variable and every randomized block encoder. Then
--
--   $$nC^{(1)}\le C^{(n)}.$$
--
--   The unrestricted block optimization includes correlated input distributions.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 5, Section III, Eq.(13): product lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section III, p.5, Eq.(13): product constructions give the n-use lower bound;
the defining supremum still ranges over arbitrary correlated block encoders. -/
theorem product_lower_bound
    {X B E : Type*} [Fintype X] [Nonempty X]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (hW : IsWiretap WB WE)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * privateInfo WB WE ≤ blockPrivate n WB WE := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
