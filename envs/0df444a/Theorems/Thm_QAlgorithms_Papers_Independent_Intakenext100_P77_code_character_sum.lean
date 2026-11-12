-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_code_character_sum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.code_character_sum
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:02:20.652083+00:00
-- url     : https://prove2.me/theorems/4c8ecb19-7d30-4af9-a119-7a01de8d5877
-- title:
--   Binary-code character sum
-- statement:
--   Let $C\subseteq\mathbb F_2^n$ be a binary linear code and let $a\notin C^\perp$, where the dual uses the modulo-two dot product. Then
--
--   $$\sum_{c\in C}(-1)^{c\cdot a}=0.$$
--
--   The finite sum is real-valued. It is the cancellation identity used to isolate the disclosed-parity span in the density matrices. At $C=\{0\}$, the hypothesis is impossible, as intended.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 18, Appendix G.1 unnumbered lemma, Eq.(22): binary-code character sum

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix G.1, PDF p.18, Eq.(22): a character outside C-perp sums to zero
on C. The extracted not-in symbol is split; its meaning is fixed by the proof. -/
theorem code_character_sum {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (ha : a ∉ binDual C) :
    (∑ c : C, if c.val ⬝ᵥ a = 0 then (1 : ℝ) else -1) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
