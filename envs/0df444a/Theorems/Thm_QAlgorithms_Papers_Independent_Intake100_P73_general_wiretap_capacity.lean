-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_general_wiretap_capacity
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.general_wiretap_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:55:36.107823+00:00
-- url     : https://prove2.me/theorems/4b697325-2910-4c48-9eae-c6b8e231f941
-- title:
--   Theorem 5: general wiretap secrecy capacity formula
-- statement:
--   Let $\mathbf B=(B^n)$ and $\mathbf E=(E^n)$ be arbitrary sequences of classical discrete channels with common input alphabet $X_n$ and output alphabets $Y_n,Z_n$. A wiretap code has a positive finite message count, stochastic encoders and pairwise disjoint Bob decoding regions; messages are uniform. Let $\epsilon_B$ be its average Bob error, $I_E=M^{-1}\sum_iD(E_{Q_i}\|M^{-1}\sum_jE_{Q_j})$, and $d_E=[M(M-1)]^{-1}\sum_{i\ne j}d(E_{Q_i},E_{Q_j})$, with $d_E=0$ when $M=1$. The capacities $C_d,C_I$ are the suprema of the liminf ordinary log message rates of code sequences with $\epsilon_B\to0$ and, respectively, $d_E\to0$ or $I_E/n\to0$. They include the operational zero-rate baseline. All distances are full L1 and all rates are in nats.
--
--   For an input-law sequence $\mathbf p=(p_n)$ and channel sequence $\mathbf W$, put $T_n(a)=\mathbb P_{p_n(x)W_x^n(y)}\{n^{-1}\log[W_x^n(y)/W_{p_n}^n(y)]>a\}$. Define $\underline I(\epsilon\mid\mathbf p,\mathbf W)=\inf\{a:\liminf_nT_n(a)\le\epsilon\}$ and $\overline I(\epsilon\mid\mathbf p,\mathbf W)=\inf\{a:\limsup_nT_n(a)\le\epsilon\}$. At $\epsilon=1$ use the strict tail bound $<1$. Spectra and numerical extrema are extended-valued.
--
--   For possibly infinite spectra, interpret $L-U$ by the finite-threshold cut
--   $$
--   \mathcal D(L,U)=\sup\{a-b:a,b\in\mathbb R,\ a<L,\ U<b\}.
--   $$
--
--   Let $A_n$ range over all auxiliary alphabet sequences, let $Q^n:A_n\to\mathcal P(X_n)$ range over all stochastic preprocessors, and let $p_n\in\mathcal P(A_n)$ be arbitrary. Use the same $Q^n$ before both channels, so $(B^nQ^n)_a(y)=\sum_x Q_a^n(x)B_x^n(y)$ and similarly for Eve. Let
--   $$
--   \Gamma=\max\left\{0,\sup_{(A_n),\mathbf p,\mathbf Q}\mathcal D\bigl(\underline I(1\mid\mathbf p,\mathbf B\mathbf Q),\overline I(0\mid\mathbf p,\mathbf E\mathbf Q)\bigr)\right\}.
--   $$
--
--   The full general-channel formula is
--   $$
--   C_d(\mathbf B,\mathbf E)=C_I(\mathbf B,\mathbf E)=\Gamma.
--   $$
--   No bound on Eve's alphabet is part of this printed theorem. It identifies full-L1 secrecy capacity with normalized-KL secrecy capacity and a general information-spectrum expression; it is not a single-letter or exponent formula.
--
--   **Formalization Note.** The direct argument immediately before the theorem proves its normalized-KL part under exponential Eve-alphabet growth. The theorem itself prints no such assumption. This proof gap is retained for independent moderation, without adding the earlier hypothesis.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 9, Theorem 5: general wiretap capacity formula

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.9, Theorem 5: full-L1 and NORMALIZED-KL capacities equal
the arbitrary-preprocessing formula. No Eve alphabet bound is printed here or
added. The preceding direct proof's finite-alphabet step is a source proof gap
left explicitly for independent moderation. -/
theorem general_wiretap_capacity {X Y Z : ℕ → Type u} [∀ k, Nonempty (X k)]
    (B : (k : ℕ) → X k → Y k → ℝ≥0∞) (E : (k : ℕ) → X k → Z k → ℝ≥0∞)
    (hB : ∀ k, IsDiscreteStochastic (B k)) (hE : ∀ k, IsDiscreteStochastic (E k)) :
    generalSecrecyCapacity false B E = generalSecrecyCapacity true B E ∧
    generalSecrecyCapacity false B E = preprocessedBound B E := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
