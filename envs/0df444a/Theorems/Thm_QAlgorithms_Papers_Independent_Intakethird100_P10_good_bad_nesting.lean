-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_good_bad_nesting
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.good_bad_nesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:36:06.275291+00:00
-- url     : https://prove2.me/theorems/728ac442-1405-4628-9e20-fe6b38d28e50
-- title:
--   Nesting of fidelity-defined good and bad sets
-- statement:
--   Let $V$ be degraded from a binary cq channel $W$ by one CPTP map acting on both letter density operators, with finite nonempty output registers. Fix $0<\beta<1/2$ and $N=2^n$. Define $\mathcal G_N(W,\beta)$ by the strict condition $\sqrt{F(W_N^{(i)})}<2^{-N^\beta}$ and let $\mathcal B_N$ be its complement. Then
--
--   $$
--   \mathcal G_N(V,\beta)\subseteq\mathcal G_N(W,\beta),\qquad
--   \mathcal B_N(W,\beta)\subseteq\mathcal B_N(V,\beta).
--   $$
--
--   These inclusions compare the actual synthesized channels at every finite dyadic blocklength; they do not make the assistance set empty.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 4, §II, unnumbered consequence of Lemma 3: nesting of good and bad sets

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.4, consequence of Lemma 3: both inclusions, with the source's operational beta range. -/
theorem good_bad_nesting {H K : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (W : BinaryCQ H) (V : BinaryCQ K) (hW : IsBinaryCQ W) (hV : IsBinaryCQ V)
    (D : Superop H K) (hD : IsChannel D) (hdeg : ∀ x, V x = D (W x))
    (n : ℕ) (beta : ℝ) (hpos : 0 < beta) (hbeta : beta < 1 / 2) :
    goodSet V n beta ⊆ goodSet W n beta ∧ badSet W n beta ⊆ badSet V n beta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
