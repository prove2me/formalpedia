-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_infinite_implies_infinitesimal
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.infinite_implies_infinitesimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:42:54.075409+00:00
-- url     : https://prove2.me/theorems/872bf185-e20d-41f1-bc8b-cacb5890a77e
-- title:
--   Remark after Definition 14 (infinite implies infinitesimal divisibility)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. If a channel $T$ has a CPTP root of every positive integer order, then
--
--   $$\bigl(\forall n\ge1\ \exists R_n\text{ CPTP}:R_n^n=T\bigr)\quad\Longrightarrow\quad T\in\overline{\mathcal I}.$$
--
--   Here $\mathcal I$ consists of channels admitting, for each $\varepsilon>0$, an exact finite product of CPTP factors at distance at most $\varepsilon$ from the identity. The bar is ambient norm closure.
--
--   This includes singular infinitely divisible channels and does not assert a finite-time continuous-generator representation.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 13, Remark after Definition 14 (infinite implies infinitesimal divisibility)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Unnumbered remark after Definition 14, PDF p.13: roots imply membership in the closure. -/
theorem infinite_implies_infinitesimal {d : ℕ} (hd : 0 < d) (T : Super d)
    (hT : InfiniteDivisible T) : Infinitesimal true T := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
