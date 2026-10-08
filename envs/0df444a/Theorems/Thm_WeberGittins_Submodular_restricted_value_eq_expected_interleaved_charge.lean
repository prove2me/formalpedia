-- Prove2me | Theorems.Thm_WeberGittins_Submodular_restricted_value_eq_expected_interleaved_charge
-- name    : WeberGittins.Submodular.restricted_value_eq_expected_interleaved_charge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:15.927636+00:00
-- url     : https://prove2.me/theorems/5afbb9a3-9c22-43df-bba7-26c84e35bee1
-- title:
--   Proof of Theorem 4, p. 1030 — $V(I)$ is the expected discounted sum of the interleaved prevailing charges
-- statement:
--   Consider $n$ bandits on a standard Borel state space $S$ with common transition kernel $P$ and measurable reward $r$, rewards nonnegative and uniformly bounded, discount factor $0<\beta<1$, and fixed initial states $x=(x_1,\dots,x_n)$. Let $\omega=(\omega_1,\dots,\omega_n)$ be a realisation of the bandits' state sequences: $\omega_1,\dots,\omega_n$ independent, $\omega_j$ a Markov chain with kernel $P$ started at $x_j$ (the states bandit $j$ passes through on its successive plays). Let $\gamma_{jk}(\omega)=\min_{0\le v\le k}\gamma(\omega_j(v))$ be the prevailing charges, $\gamma$ the fair charge, and $U_t(I)(\omega)$ the sum of the first $t$ terms of the nonincreasing interleaving of the sequences $(\gamma_{jk}(\omega))_{k\ge0}$, $j\in I$. Then for every set of bandits $I$,
--   $$
--   V(I)=\mathbb E\Big[\sum_{t=0}^\infty\beta^t\big(U_{t+1}(I)-U_t(I)\big)\Big],
--   $$
--   where $V(I)$ is the maximal expected total-discounted reward of the restricted problem $P(I)$.
--
--   The increment $U_{t+1}(I)-U_t(I)$ is the charge paid at time $t$ when $P(I)$ is played optimally, so the identity says that the optimal value of $P(I)$ equals the expected total-discounted charge, the fair-game property behind Weber's proof of the Gittins index theorem. Weber's proof of Theorem 4 uses it when it "multiplies (10) by $\beta^t$, sums on $t$ and takes an expected value over realisations".
--
--   **Formalization Note** The law of the realisation is the product `Measure.pi (fun j => markovChainMeasure P (x j))`, and $\gamma_{jk}$ is `prevailingChargeStack`, exactly the product measure and the charge stacks of the published finite-horizon coupling identity `BanditAlgorithm.gittins_finite_prevailing_charge_eq_stack_coupling_value`. Weber states the identity implicitly ("the sum of undiscounted charges paid while playing $P(I)$ optimally"); the Lean makes it explicit. The discounted charge uses increments of $U_t$: $\sum_t\beta^tU_t(I)$ would differ by the factor $\beta/(1-\beta)$. For $I=\emptyset$ both sides are $0$. The standing assumptions of p. 1024 (nonnegative, uniformly bounded rewards) and `StandardBorelSpace S`, `Measurable r` are hypotheses.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1030, proof of Theorem 4 ("The theorem follows by multiplying (10) by β^t, summing on t from 0 to infinity and taking an expected value over realisations"); pp. 1026–1027, proof of Theorem 1 ("Thus we have a fair game")

import Definitions.Def_WeberGittins_Submodular_Model
import Definitions.Def_WeberGittins_Submodular_PartialInterleavedSum

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Submodular

/-- Weber (1992), proof of Theorem 4, p. 1030: `V(I)` is the expected total-discounted charge paid
when the prevailing-charge sequences of the bandits of `I` are interleaved into nonincreasing order,
the expectation taken over the realisations `ω` of the bandits' state sequences (independent Markov
chains, bandit `j` started at `x j`). The charge paid at time `t` is the `(t+1)`-st element of the
interleaving, `U_{t+1}(I) − U_t(I)`. -/
theorem restricted_value_eq_expected_interleaved_charge {n : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → S)
    (I : Finset (Fin n)) :
    restrictedValue P r β x I =
      ∫ ω, ∑' t : ℕ, β ^ t *
          (partialInterleavedSum (prevailingChargeStack P r β ω) I (t + 1) -
            partialInterleavedSum (prevailingChargeStack P r β ω) I t)
        ∂(Measure.pi fun j => markovChainMeasure P (x j)) := by sorry

end WeberGittins.Submodular
