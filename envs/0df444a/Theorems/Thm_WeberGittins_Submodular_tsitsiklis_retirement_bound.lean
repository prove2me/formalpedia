-- Prove2me | Theorems.Thm_WeberGittins_Submodular_tsitsiklis_retirement_bound
-- name    : WeberGittins.Submodular.tsitsiklis_retirement_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:34.510738+00:00
-- url     : https://prove2.me/theorems/e7c48d4f-d4a4-4f89-b3e5-ad5e940c99d7
-- title:
--   Section 5, p. 1030 (Tsitsiklis 1986) — with a retirement bandit paying $(1-\beta)M$ per play, $V(S)\le V(\{i,1\})+V(S\setminus\{i\})-M$
-- statement:
--   Consider $n$ bandits as in Theorem 4 (standard Borel state space $S$, common kernel $P$, measurable reward $r$, rewards nonnegative and uniformly bounded, $0<\beta<1$, initial states $x$), and let $S_{\rm b}=\{1,\dots,n\}$ be the set of all bandits. Suppose one bandit $b$ always pays $(1-\beta)M$ per play: it starts in a state $y_0$ that it never leaves ($P(y_0,\cdot)=\delta_{y_0}$) and $r(y_0)=(1-\beta)M$. Playing $b$ forever earns $M$, so choosing it amounts to taking a retirement option. Then for every bandit $i\ne b$,
--   $$
--   V(S_{\rm b})\le V(\{i,b\})+V(S_{\rm b}\setminus\{i\})-M .
--   $$
--
--   This special case of Theorem 4 (take $I=\{i,b\}$, $J=S_{\rm b}\setminus\{i\}$, so $V(I\cap J)=V(\{b\})=M$) was proved earlier by Tsitsiklis (1986). It bounds the value of the whole problem by values of smaller problems.
--
--   **Formalization Note** The paper's "bandit 1" is an arbitrary index $b$. "Always pays $(1-\beta)M$ per play" is encoded in the common-kernel model by an absorbing initial state with reward $(1-\beta)M$. $M\ge0$ follows from nonnegative rewards. The set of all bandits, the paper's $S$, is `Finset.univ`.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1030, Section 5 (Tsitsiklis's special case of (9))

import Definitions.Def_WeberGittins_Submodular_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Submodular

/-- Weber (1992), Section 5, p. 1030 (Tsitsiklis 1986): if bandit `b` always pays `(1 − β)M` per
play (it starts in an absorbing state `y₀` with reward `(1 − β)M`), so that playing it amounts to
retirement, then for every other bandit `i`,
`V(S) ≤ V({i, b}) + V(S \ {i}) − M`. -/
theorem tsitsiklis_retirement_bound {n : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → S)
    {y₀ : S} {M : ℝ} (hy₀ : P y₀ = Measure.dirac y₀) (hry₀ : r y₀ = (1 - β) * M)
    (b i : Fin n) (hb : x b = y₀) (hib : i ≠ b) :
    restrictedValue P r β x Finset.univ ≤
      restrictedValue P r β x {i, b} + restrictedValue P r β x (Finset.univ \ {i}) - M := by sorry

end WeberGittins.Submodular
