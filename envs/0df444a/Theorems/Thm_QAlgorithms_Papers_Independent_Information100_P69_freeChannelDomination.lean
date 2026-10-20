-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_freeChannelDomination
-- name    : QAlgorithms.Papers.Independent.Information100.P69.freeChannelDomination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:02:09.433827+00:00
-- url     : https://prove2.me/theorems/09e4bd9b-476f-4d13-a3d1-0ea75f38639e
-- title:
--   Free-channel domination
-- statement:
--   Fix nonzero local dimensions, positive witness minimum eigenvalues $t,w$, and $0<\varepsilon<1$. There is a finite $K_\varepsilon\ge0$, uniform over targets, families, and witnesses with these eigenvalues, such that the following holds for every family satisfying F1–F5 with witnesses $\tau,\omega$. At every $n\ge1$ and $0<\delta\le1/16$, some $S_n\in\mathcal F_n$ and CPTP $L_n$ satisfy
--   $$S_n\ge_{\rm CP}\beta_{\varepsilon,n}2^{-g_\varepsilon(n,\delta)}L_n,\qquad\|L_n-\mathcal N^{\otimes n}\|_\diamond\le\delta,$$
--   where $g_\varepsilon(n,\delta)=K_\varepsilon n^{2/3}\log_2((n+1)/\delta)$. The constant precedes all variable block data. This quantitative completion bound applies in every regime of length and accuracy.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 19, Theorem 16

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Theorem 16, constant uniform over targets, families and witness eigenbases, PDF pp.19–20.
Exact positive minimum eigenvalues are fixed before the constant. -/
theorem freeChannelDomination [Nonempty A] [Nonempty B] (t w eps : ℝ) (ht : 0 < t) (hw : 0 < w)
    (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (tau : Matrix A A ℂ) (omega : Matrix B B ℂ),
      minPositiveEigenvalue tau = t → minPositiveEigenvalue omega = w →
      ∀ F : BlockFamily A B, Admissible F omega → Additional F tau →
      ∀ N : Superop A B, IsChannel N → ∀ n, 1 ≤ n → ∀ delta : ℝ, 0 < delta → delta ≤ 1/16 →
        ∃ S ∈ F n, ∃ L : Superop (Sites A n) (Sites B n), IsChannel L ∧
          CPLe (((beta (power N n) (F n) eps*Real.rpow 2 (-overhead K n delta):ℝ):ℂ) • L) S ∧
          diamond (L-power N n) ≤ delta := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
