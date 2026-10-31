-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_wiretap_direct
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.wiretap_direct
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:54:27.406023+00:00
-- url     : https://prove2.me/theorems/dd34c2bb-a3c6-46ed-92da-1c54098770f0
-- title:
--   Lemma 4: general wiretap direct bounds
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
--   For every normalized input-law sequence $\mathbf p$,
--   $$
--   C_d(\mathbf B,\mathbf E)\ge\mathcal D\bigl(\underline I(1\mid\mathbf p,\mathbf B),\overline I(0\mid\mathbf p,\mathbf E)\bigr).
--   $$
--   If, additionally, $|Z_n|=d^n$ for a fixed positive integer $d$, then
--   $$
--   C_I(\mathbf B,\mathbf E)\ge\mathcal D\bigl(\underline I(1\mid\mathbf p,\mathbf B),\overline I(0\mid\mathbf p,\mathbf E)\bigr).
--   $$
--   The alphabet assumption belongs only to the second inequality. These direct bounds apply to arbitrary channel sequences and retain the paper's normalized-KL secrecy criterion.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 9, Lemma 4, (30)–(31): general wiretap direct bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.9, Lemma 4, (30)–(31): exponential Eve alphabet assumption
applies ONLY to the normalized-KL clause. Infinite differences use finite cuts. -/
theorem wiretap_direct {X Y Z : ℕ → Type*} [∀ k, Nonempty (X k)]
    (B : (k : ℕ) → X k → Y k → ℝ≥0∞) (E : (k : ℕ) → X k → Z k → ℝ≥0∞)
    (hB : ∀ k, IsDiscreteStochastic (B k)) (hE : ∀ k, IsDiscreteStochastic (E k))
    (p : (k : ℕ) → PMF (X k)) :
    spectralDifference (epsilonInformationSpectrum false B p 1) (epsilonInformationSpectrum true E p 0) ≤ generalSecrecyCapacity false B E ∧
    (∀ d : ℕ, 0 < d → (∀ k, Nat.card (Z k) = d ^ length k) →
      spectralDifference (epsilonInformationSpectrum false B p 1) (epsilonInformationSpectrum true E p 0) ≤ generalSecrecyCapacity true B E) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
