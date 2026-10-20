-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_traceDefectCompletion
-- name    : QAlgorithms.Papers.Independent.Information100.P69.traceDefectCompletion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:56:40.629833+00:00
-- url     : https://prove2.me/theorems/4886c071-41f4-4a99-a6dc-1302bde77b83
-- title:
--   Completion at the cost of the trace defect
-- statement:
--   At positive blocklength $n$, assume only that the free set consists of channels, is convex, and contains the faithful replacer $R_\omega^{\otimes n}$. Let $Q$ be CP and trace nonincreasing, with $Q\le_{\rm CP}\lambda M$, $M\in\mathcal F_n$, and $\lambda\ge1$. Define $D=I-Q^\dagger(I)$, $d=\|D\|_\infty$,
--   $$L(X)=Q(X)+\operatorname{Tr}(DX)\omega^{\otimes n},\quad S=\frac{\lambda M+dR_\omega^{\otimes n}}{\lambda+d}.$$
--   Then $L$ is CPTP, $S$ is free, and
--   $$L\le_{\rm CP}(\lambda+d)S,\quad\|L-\mathcal N^{\otimes n}\|_\diamond\le2\|Q-\mathcal N^{\otimes n}\|_\diamond,\quad0\le d\le\min\{1,\|Q-\mathcal N^{\otimes n}\|_\diamond\}.$$
--   This restores trace preservation at a cost measured by the actual defect, including $d=0$.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 11, Lemma 7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 7, explicit trace-defect completion and free mixture, PDF p.11. -/
theorem traceDefectCompletion [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (n : ℕ) (hn : 1 ≤ n)
    (F : Set (Superop (Sites A n) (Sites B n))) (hF : Convex ℝ F)
    (hchan : ∀ M ∈ F, IsChannel M) (omega : Matrix B B ℂ) (homega : Faithful omega)
    (hR : power (replacer omega) n ∈ F)
    (Q : Superop (Sites A n) (Sites B n)) (hQ : CP Q) (hdef : (defect Q).PosSemidef)
    (M : Superop (Sites A n) (Sites B n)) (hM : M ∈ F)
    (lam : ℝ) (hlam : 1 ≤ lam) (hdom : CPLe Q ((lam:ℂ) • M)) :
    let D := defect Q
    let d := specNorm D
    let L := complete Q D (matrixPower omega n)
    let S := ((lam+d:ℂ)⁻¹) • ((lam:ℂ) • M + (d:ℂ) • power (replacer omega) n)
    IsChannel L ∧ S ∈ F ∧ CPLe L ((lam+d:ℂ) • S) ∧
      diamond (L-power N n) ≤ 2*diamond (Q-power N n) ∧
      0 ≤ d ∧ d ≤ min 1 (diamond (Q-power N n)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
