-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_entropyComparison
-- name    : QAlgorithms.Papers.Independent.Information100.P69.entropyComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:59:05.782029+00:00
-- url     : https://prove2.me/theorems/9a99680b-3926-40d8-b986-e5ddc664b9a0
-- title:
--   Entropy comparison
-- statement:
--   Fix a CPTP target $\mathcal N$ and a positive blocklength $n$. Assume the block free set is convex and contains $R_\omega^{\otimes n}$ for faithful $\omega$. Put $a=\dim A$, $b=\dim B$, and $C=\log_2 b-\log_2\lambda_{\min}(\omega)$. If $L$ is CPTP, $S$ is free, $L\le_{\rm CP}2^zS$, and $\|L-\mathcal N^{\otimes n}\|_\diamond\le\delta\le1$ with $\delta\ge0$, then
--   $$E_n\le z+1+\frac\delta2\big[n(C+\log_2(ab))+1\big]+h_2(\delta/2).$$
--   Here $z$ is real and $h_2$ is binary entropy in bits. This compares optimized entropy with a CPTP approximation cost using the full diamond norm.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 15, Lemma 10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 10, delta/2 multiplies the whole bracket including its +1, PDF p.15. -/
theorem entropyComparison [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (omega : Matrix B B ℂ) (homega : Faithful omega) (n : ℕ) (hn : 1 ≤ n)
    (G : Set (Superop (Sites A n) (Sites B n))) (hG : Convex ℝ G)
    (hGchan : ∀ M ∈ G, IsChannel M) (hR : power (replacer omega) n ∈ G)
    (L S : Superop (Sites A n) (Sites B n)) (hL : IsChannel L) (hS : S ∈ G)
    (z delta : ℝ) (hdom : CPLe L ((Real.rpow 2 z:ℂ) • S))
    (herr : diamond (L-power N n) ≤ delta) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    resourceEntropy (power N n) G ≤ ENNReal.ofReal
      (z+1+delta/2*((n:ℝ)*(capacity omega+Real.logb 2 (Fintype.card A*Fintype.card B))+1)+binEntropy2 (delta/2)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
