-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_3_4
-- name    : PriceIgnorance.Pairwise.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:32.59602+00:00
-- url     : https://prove2.me/theorems/3d869312-6eeb-40a0-90ee-407406a67796
-- title:
--   Lemma 3.4 — with finitely supported marginals, $kI$ laws and randomized algorithms are finite mixtures
-- statement:
--   Fix $k$ and finitely supported marginals $D_1,\dots,D_n$ of nonnegative values. Then:
--
--   1. there are finitely many $D^{(1)},\dots,D^{(m)}\in kI(D_1,\dots,D_n)$ such that every $D\in kI(D_1,\dots,D_n)$ is a convex combination of them, $D=\sum_j w_jD^{(j)}$ with $w_j\ge0$ and $\sum_jw_j=1$;
--   2. in fixed order, there are finitely many deterministic online algorithms $A_1,\dots,A_s$ such that for every randomized online algorithm $A$ there are weights $w_l\ge0$ with $\sum_lw_l=1$ and
--   $$\mathrm{val}(A,v)=\sum_{l=1}^sw_l\,\mathrm{val}(A_l,v)\qquad\text{for every }v\in\mathrm{supp}(D_1)\times\dots\times\mathrm{supp}(D_n);$$
--   3. the same holds in uniformly random order (prophet secretary), with $\mathrm{val}$ averaged over the order.
--
--   This finiteness is what lets the proof of Theorem 3.1 apply von Neumann's finite minimax theorem (Lemma 3.2).
--
--   Differences from the source:
--   - encoding: D_1..D_n have finite support → value laws carried by a finite set; the support grid is {v : D_i({v_i}) > 0 ∀ i}; reason: standing assumption that values are nonnegative (p. 1); the support of a finitely supported law is its set of atoms
--   - encoding: D is a convex combination of D(1)..D(m) → D = Σ_j (w_j : ℝ≥0∞) • D(j) with w : Fin m → ℝ≥0, Σ w = 1; reason: equality of measures; same notion
--   - reading: algorithms run on such distributions are convex combinations of finitely many deterministic algorithms → the value function v ↦ val(A,v) equals a convex combination of the value functions of fixed deterministic algorithms at every v in the support grid; reason: algorithms run on such distributions only meet value vectors in the support grid, and enter every ratio only through val
--   - reading: algorithms (stated in the prophet context) → clauses for fixed order and for uniformly random order; reason: the proof of Theorem 3.1 uses the lemma for prophet secretary too, by overloading val (p. 7)
--   - encoding: randomized online algorithms (mixtures of deterministic ones) → behavioural stopping probabilities p_i(history) ∈ [0,1], measurable in the history; reason: same value functions as mixtures of deterministic rules (Kuhn); measurability makes E_D[val] defined
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 6, Lemma 3.4 (proof p. 27)

import Mathlib
import Definitions.Def_PriceIgnorance_Pairwise_Instance
import Definitions.Def_PriceIgnorance_Pairwise_Algorithms

open MeasureTheory
open scoped NNReal ENNReal

namespace PriceIgnorance.Pairwise

/-- Lemma 3.4 (p. 6): for finitely supported marginals `D_1, …, D_n`, (a) there are finitely many
`D^{(1)}, …, D^{(m)} ∈ kI(D_1, …, D_n)` of which every `D ∈ kI(D_1, …, D_n)` is a convex
combination, and (b) there are finitely many deterministic algorithms of which every randomized
algorithm is a convex combination on the support grid, for fixed and for random arrival order. -/
theorem lemma_3_4 (k : ℕ) {n : ℕ} (Dm : Fin n → Measure ℝ) (hlaw : ∀ i, IsValueLaw (Dm i))
    (hfin : ∀ i, HasFiniteSupport (Dm i)) :
    (∃ (m : ℕ) (Dv : Fin m → Measure (Fin n → ℝ)), (∀ j, Dv j ∈ kI Dm k) ∧
      ∀ D ∈ kI Dm k, ∃ w : Fin m → ℝ≥0, ∑ j, w j = 1 ∧ D = ∑ j, (w j : ℝ≥0∞) • Dv j) ∧
    (∃ (s : ℕ) (Ad : Fin s → OnlineAlg n), (∀ l, (Ad l).IsDeterministic) ∧
      ∀ A : OnlineAlg n, ∃ w : Fin s → ℝ, (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
        ∀ v ∈ supportGrid Dm, A.val v = ∑ l, w l * (Ad l).val v) ∧
    (∃ (s : ℕ) (Ad : Fin s → OnlineAlgRO n), (∀ l, (Ad l).IsDeterministic) ∧
      ∀ A : OnlineAlgRO n, ∃ w : Fin s → ℝ, (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
        ∀ v ∈ supportGrid Dm, A.val v = ∑ l, w l * (Ad l).val v) := by sorry

end PriceIgnorance.Pairwise
