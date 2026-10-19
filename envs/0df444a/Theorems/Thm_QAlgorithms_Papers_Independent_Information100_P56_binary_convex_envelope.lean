-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_binary_convex_envelope
-- name    : QAlgorithms.Papers.Independent.Information100.P56.binary_convex_envelope
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:16:11.720297+00:00
-- url     : https://prove2.me/theorems/3fb08c60-ff62-4338-98bd-cb8247a1c915
-- title:
--   Lemma III.1: binary-input convex-envelope formula
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. For an arbitrary binary-input channel, let $\Delta(x)$ be the average-output entropy difference under $\operatorname{Bern}(x)$. Define $\Delta_{\rm vex}(x)$ by minimizing $\sum_vp_v\Delta(x_v)$ over finite probability weights, $x_v\in[0,1]$, and $\sum_vp_vx_v=x$. Then
--
--   $$C^{(1)}=\max_{0\le x\le1}\{\Delta(x)-\Delta_{\rm vex}(x)\},\qquad C^{(1)}=0\iff\Delta\text{ is convex on }[0,1].$$
--
--   The maximum is attained, and each envelope value is attained with at most two support points. This describes all finite auxiliary preprocessing, without a covariance assumption.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 6, Lemma III.1: binary-input convex-envelope formula

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma III.1, p.6: binary convex-envelope formula, attained maximum and two-point
envelope attainment, and the exact zero-private-information criterion. -/
theorem binary_convex_envelope
    {B E : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (WB : Bool → Matrix B B ℂ) (WE : Bool → Matrix E E ℂ) (hW : IsWiretap WB WE) :
    let f := binaryDelta WB WE
    (∃ x ∈ Set.Icc (0 : ℝ) 1,
      privateInfo WB WE = f x - convexEnvelope f x ∧
      ∀ y ∈ Set.Icc (0 : ℝ) 1, f y - convexEnvelope f y ≤ privateInfo WB WE) ∧
    (privateInfo WB WE = 0 ↔ ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ a ∈ Set.Icc (0 : ℝ) 1,
      ∃ b ∈ Set.Icc (0 : ℝ) 1, ∃ w ∈ Set.Icc (0 : ℝ) 1,
        w * a + (1 - w) * b = x ∧
        convexEnvelope f x = w * f a + (1 - w) * f b) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
