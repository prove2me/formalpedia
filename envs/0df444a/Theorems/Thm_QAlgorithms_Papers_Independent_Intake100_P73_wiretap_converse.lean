-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_wiretap_converse
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.wiretap_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:55:00.389985+00:00
-- url     : https://prove2.me/theorems/94311298-28fc-4095-a0c9-089b171c8ad0
-- title:
--   Lemma 5: both wiretap converses via stochastic preprocessing
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
--   Then both converse inequalities hold:
--   $$
--   C_d(\mathbf B,\mathbf E)\le\Gamma,\qquad C_I(\mathbf B,\mathbf E)\le\Gamma.
--   $$
--   The optimization is over arbitrary stochastic channels and arbitrary auxiliary laws and alphabets, without alphabet growth or memorylessness assumptions. This is a converse for both secrecy criteria.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 9, Lemma 5, (32)–(33): general wiretap converse via preprocessing

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.9, Lemma 5, (32)–(33): both converses optimize arbitrary
auxiliary alphabets, laws and stochastic preprocessing. The proof's displayed
R=... gives only the stated R<=...; no equality hypothesis is inserted. -/
theorem wiretap_converse {X Y Z : ℕ → Type u} [∀ k, Nonempty (X k)]
    (B : (k : ℕ) → X k → Y k → ℝ≥0∞) (E : (k : ℕ) → X k → Z k → ℝ≥0∞)
    (hB : ∀ k, IsDiscreteStochastic (B k)) (hE : ∀ k, IsDiscreteStochastic (E k)) :
    generalSecrecyCapacity false B E ≤ preprocessedBound B E ∧
    generalSecrecyCapacity true B E ≤ preprocessedBound B E := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
