-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_freeMultipliers
-- name    : QAlgorithms.Papers.Independent.Information100.P69.freeMultipliers
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:09:56.722301+00:00
-- url     : https://prove2.me/theorems/6b499e35-2cee-43e0-aad0-1a54e414809c
-- title:
--   Free multipliers
-- statement:
--   Assume F1–F5 with local dimensions $a,d$ and faithful witnesses with minimum eigenvalues $t,w$. Suppose $M\in\mathcal F_n$, $p>0$, and $M\ge_{\rm CP}p\operatorname{Ad}_K$. Let $O=\sum_i c_iF_i$ be a finite output-contraction expansion with chosen support sizes $r_i$. Define
--   $$h_r=(ad)^r[(at)(dw)]^{-r/2},\qquad H=\sum_i|c_i|h_{r_i}.$$
--   If $H>0$, there exists $M'\in\mathcal F_n$ with
--   $$M'\ge_{\rm CP}\frac{p}{H^2}\operatorname{Ad}_{OK}.$$
--   There is no restriction $p\le1$. This turns local corrections into free domination with their squared weighted coefficient cost.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 32, Lemma 28

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 28, arbitrary positive branch coefficient, chosen supports and squared total
multiplier cost, PDF pp.32–33. -/
theorem freeMultipliers [Nonempty A] [Nonempty B] (F : BlockFamily A B) (tau : Matrix A A ℂ) (omega : Matrix B B ℂ)
    (hF : Admissible F omega) (hextra : Additional F tau) (n : ℕ) (hn : 1 ≤ n)
    (M : Superop (Sites A n) (Sites B n)) (hM : M ∈ F n)
    (p : ℝ) (hp : 0 < p) (K : Matrix (Sites B n) (Sites A n) ℂ)
    (hdom : CPLe ((p:ℂ) • conjSuperop K) M) (P : LocalExpansion B n)
    (hcost : 0 < weightedCost (Fintype.card A) (minPositiveEigenvalue tau) (minPositiveEigenvalue omega) P) :
    ∃ M' ∈ F n, CPLe
      (((p / (weightedCost (Fintype.card A) (minPositiveEigenvalue tau)
        (minPositiveEigenvalue omega) P)^2:ℝ):ℂ) • conjSuperop (P.operator*K)) M' := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
