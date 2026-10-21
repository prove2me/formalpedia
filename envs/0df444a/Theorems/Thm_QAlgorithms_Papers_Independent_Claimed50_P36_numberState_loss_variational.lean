-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P36_numberState_loss_variational
-- name    : QAlgorithms.Papers.Independent.Claimed50.P36.numberState_loss_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:32:44.106347+00:00
-- url     : https://prove2.me/theorems/53a821c6-8ec6-4643-8252-6f9b72c0fd9c
-- title:
--   Number-state pure-loss constrained Holevo maximum
-- statement:
--   Let $\eta\in[0,1]$ be photon survival probability and $m\ge0$ the transmitted mean photon budget. There is no added noise. The input letters are all number states $|n\rangle$, and the output of letter $n$ is diagonal with probabilities
--
--   $$
--   W_\eta(y\mid n)=\begin{cases}\binom ny\eta^y(1-\eta)^{n-y},&0\le y\le n,\\0,&y>n.\end{cases}
--   $$
--
--   For a probability law $p$ with finite mean at most $m$, set $q_p(y)=\sum_n p_nW_\eta(y\mid n)$. With natural-log entropy $H$, the product-letter, collective-receiver classical capacity is the attained maximum
--
--   $$
--   C_\eta(m)=\max_{p:\,\sum_n n p_n\le m}\left[H(q_p)-\sum_n p_nH(W_\eta(\cdot\mid n))\right].
--   $$
--
--   The output law has mean at most $\eta m$; its entropy and the averaged conditional entropy are finite. The maximizing law is asserted to exist, but is not evaluated.
--
--   This is the variational capacity formula the paper explicitly leaves unsolved. Its $\eta$ equals the square of the amplitude attenuation used in the Gaussian subsection.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, PDF p. 15, Eqs.(60)-(63)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF p.15, Eqs.(60)-(63): the constrained Holevo maximum equals operational
capacity for pure photon loss on number letters. Attainment is a conclusion.
eta is photon survival probability; the Gaussian section's amplitude is sqrt eta.
This does not claim an explicit solution of the optimization. -/
theorem numberState_loss_variational (eta m : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hm : 0 ≤ m) :
    BddAbove (numberRates eta m) ∧
    (∀ p : ℕ → ℝ, NumberLaw m p →
      NumberLaw (eta * m) (lossOutput eta p) ∧
      numberEntropy (lossOutput eta p) ≠ ⊤ ∧
      (∀ n, numberEntropy (lossTransition eta n) ≠ ⊤) ∧
      Summable (fun n => p n * (numberEntropy (lossTransition eta n)).toReal)) ∧
    ∃ p : ℕ → ℝ, NumberLaw m p ∧
      numberCapacity eta m = numberHolevo eta p ∧
      ∀ q : ℕ → ℝ, NumberLaw m q → numberHolevo eta q ≤ numberHolevo eta p := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P36

end
