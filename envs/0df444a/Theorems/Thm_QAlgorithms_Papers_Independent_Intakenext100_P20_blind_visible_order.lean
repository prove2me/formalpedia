-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_blind_visible_order
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.blind_visible_order
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:34:47.941182+00:00
-- url     : https://prove2.me/theorems/8c55e4a3-3d79-4f53-8a7f-e2e27025c299
-- title:
--   Code inclusion and exponent order (8)–(9)
-- statement:
--   Let $\Xi$ be an arbitrary discrete label set and let $\mathcal H$ be a nonzero finite-dimensional complex Hilbert space. The source consists of normalized pure states $\rho_i$ and probabilities $p_i\ge0$ with $\sum_i p_i=1$; write $\rho_p=\sum_i p_i\rho_i$. Each memory space is finite and nonzero. Blind encoders and decoders are CPTP; a visible encoder maps labels to normalized density operators. A blind encoder is fixed before its input label.
--
--   For positive block length $n$, the word probabilities and states are the independent products of the source probabilities and states. Admissible code sequences satisfy $\limsup_n n^{-1}\log\dim\mathcal K_n\le R$. An error exponent is the supremum over admissible sequences of $\liminf_n -n^{-1}\log\epsilon_n$; a success exponent is the infimum of $\liminf_n -n^{-1}\log(1-\epsilon_n)$. Logarithms are natural, and $-\log0=+\infty$.
--
--   For every blind code $(\mathcal K,E,D)$, the visible encoder $F(i)=E(\rho_i)$ uses the same memory and decoder and has exactly the same average overlap error. Consequently,
--
--   $$r_{e,B}(R)\le r_{e,V}(R),\qquad r^*_{e,B}(R)\ge r^*_{e,V}(R).$$
--
--   These comparisons express inclusion of blind codes in the visible model.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 2, Code inclusion and exponent order (8)–(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- PDF pp.2-3, code inclusion and (8)-(9): every fixed blind encoder induces
an equally sized visible encoder with identical error, hence the two exponent orders. -/
theorem blind_visible_order {L : Type*} {d : ℕ} (S : DiscretePureSource L d) (R : ℝ) :
    (∀ C : BlindCode (Fin d),
      ∃ F : L → Matrix (Fin C.memory) (Fin C.memory) ℂ,
        (∀ i, IsDensityMatrix (F i)) ∧ F = (fun i => C.encode (S.state i)) ∧
        averageLoss S.weight S.state (fun i => C.decode (F i)) false =
          averageLoss S.weight S.state (fun i => C.decode (C.encode (S.state i))) false) ∧
    blindExponent S R false false ≤ visibleExponent S R false false ∧
    visibleExponent S R false true ≤ blindExponent S R false true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
