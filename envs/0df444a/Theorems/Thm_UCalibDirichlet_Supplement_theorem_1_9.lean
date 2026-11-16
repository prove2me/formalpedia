-- Prove2me | Theorems.Thm_UCalibDirichlet_Supplement_theorem_1_9
-- name    : UCalibDirichlet.Supplement.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:13:01.822011+00:00
-- url     : https://prove2.me/theorems/054be96a-29de-4b21-8835-dd746ba97f41
-- title:
--   Theorem 1.9 — $K$-gap is real: Algorithm 1 has regret $\Omega(KT^{1-1/K})$ on $F_K$, minimax regret $\Theta(T^{1-1/K})$
-- statement:
--   Let $K\ge 3$ and consider the convex potential
--   $$F_K(p)=1-\Big(K\min_{j\in[K]}p_j\Big)^{1/K}$$
--   on the simplex $\Delta_K$, and a proper loss $\ell_F$ (with finite Bayes risk) whose Bayes risk is $-F_K$. There are universal constants $c>0$ and $C$ such that for every $K\ge 3$, every $T\ge K$ and every such loss:
--
--   1. on the outcome sequence $1,1,\dots,1$ ($T-K+1$ ones), $2,\dots,K$, Algorithm 1 suffers expected regret
--   $$\mathrm{Reg}_F(T)\ \ge\ c\,K\,T^{1-1/K};$$
--   2. the minimax regret satisfies
--   $$c\,T^{1-1/K}\ \le\ R^*_F(T)\ \le\ C\,T^{1-1/K}.$$
--
--   So the factor $K$ in the upper bound of Theorem 1.8 cannot be removed for Algorithm 1: on this loss it is suboptimal by a factor of order $K$.
--
--   **Formalization Note** The constants are universal (independent of $K$, $T$ and the loss), quantified first. Rounds and labels are $0$-based; the sequence is the definition `seq19`. The minimax regret is taken over forecasters whose expected losses are defined.
--
--   Differences from the source:
--   - reading: Reg_F = Ω(K T^{1−1/K}) and minimax regret Θ(T^{1−1/K}), constants unspecified → one pair of constants c > 0, C quantified before K, T and the loss; reason: the theorem is about the K-dependence (a K-dependent constant would make the gap empty); the proof's constants in (52), (53), (59) are K-free
--   - encoding: the loss ℓ_F with convex potential F → every proper loss with finite Bayes risk whose potential bayesPot equals F_K on Δ_K; reason: every proper loss with potential F is an ℓ_F for some subgradient choice (display (3)); the paper leaves the choice at tied minima open (p.33: ties have probability zero)
--   - encoding: the outcome sequence 1, …, 1 (T − K + 1 ones), 2, …, K → seq19 K T with 0-based labels, and T ≥ K; reason: the sequence exists only for T ≥ K (the proof assumes it); labels j ↦ j − 1
--   - encoding: minimax regret → minimaxRegret: infimum over forecasters (laws on Δ_K per history) with a.e.-measurable losses, supremum over fixed outcome sequences, in EReal; reason: the base model's forecaster and regret; the expectations in (2) presuppose the measurability
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.9, pp.6–7 (proof pp.33–36, displays (50)–(59))

import Mathlib
import Definitions.Def_UCalibDirichlet_IsProperLoss
import Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
import Definitions.Def_UCalibDirichlet_bayesPot
import Definitions.Def_UCalibDirichlet_regret
import Definitions.Def_UCalibDirichlet_alg1
import Definitions.Def_UCalibDirichlet_Supplement_minimaxRegret
import Definitions.Def_UCalibDirichlet_Supplement_FK
import Definitions.Def_UCalibDirichlet_Supplement_seq19

namespace UCalibDirichlet.Supplement

/-- **Theorem 1.9 (K-gap is real).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Theorem 1.9, pp.6–7: "For `K ≥ 3`, consider the loss function `ℓ_F` with a convex
potential `F(p) = 1 − (K min_{j∈[K]} p_j)^{1/K}`. Then, for the outcome sequence `1, 1, …, 1`
(`T − K + 1` ones), `2, …, K`, Algorithm 1 suffers regret `Reg_F = Ω(K T^{1−1/K})`. On the other
hand, the minimax regret for this loss is `Θ(T^{1−1/K})`."

There are universal constants `c > 0` and `C` such that for every `K ≥ 3`, every `T ≥ K` and every
proper loss `ℓ` with finite Bayes risk whose potential is `F_K` on `Δ_K`:
1. Algorithm 1 has expected regret at least `c K T^{1−1/K}` on the sequence of Theorem 1.9;
2. the minimax regret satisfies `c T^{1−1/K} ≤ R*(T) ≤ C T^{1−1/K}`.

**Formalization Note.** `Ω` and `Θ` are read with constants independent of `K` and `T`, quantified
first: the theorem is a statement about the `K`-dependence (a `K`-dependent constant would make
the gap claim empty), and the proof's constants are `K`-free ((52), (53), (59), pp.34–36). `T ≥ K`
is the range in which the sequence exists (the proof uses it). The loss `ℓ_F` is any proper loss
with finite Bayes risk and potential `F_K`: the paper leaves the loss at tied minimizing
coordinates unspecified (p.33: ties have probability zero), and elsewhere it is determined by
`F_K`. The sequence is `seq19` (0-based labels). -/
theorem theorem_1_9 : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ,
    ∀ (K : ℕ) (hK : 3 ≤ K) (T : ℕ), K ≤ T →
    ∀ ℓ : (Fin K → ℝ) → Fin K → EReal, IsProperLoss ℓ → HasFiniteBayesRisk ℓ →
      (∀ q ∈ stdSimplex ℝ (Fin K), bayesPot ℓ q = FK K q) →
      (((c * K * (T : ℝ) ^ (1 - 1 / (K : ℝ)) : ℝ) : EReal) ≤
          regret ℓ alg1 (seq19 K T (by omega))) ∧
        (((c * (T : ℝ) ^ (1 - 1 / (K : ℝ)) : ℝ) : EReal) ≤ minimaxRegret ℓ T) ∧
        minimaxRegret ℓ T ≤ ((C * (T : ℝ) ^ (1 - 1 / (K : ℝ)) : ℝ) : EReal) := by sorry

end UCalibDirichlet.Supplement
