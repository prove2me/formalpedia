-- Prove2me | Theorems.Thm_SimpleMechMRF_definition_7_property
-- name    : SimpleMechMRF.definition_7_property
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:49.133577+00:00
-- url     : https://prove2.me/theorems/fdf2c4be-5176-4268-afc8-a0290a4eb08d
-- title:
--   Definition 7 property, p.10 — best conditional price revenue $=\sum f_i(t_i\mid t_{-i})\varphi_i^+$ (corrected: $\ge$-tail on $R_i$)
-- statement:
--   Let $D$ be a finite type distribution, $i$ an item and $t\in T$. Then
--
--   $$
--   \sup_{p\ge\max_{j\ne i}t_j}\;p\cdot\Pr\big[t_i\ge p\wedge(t_i,t_{-i})\in R_i\;\big|\;t_{-i}\big]\;=\;\sum_{t_i:\,(t_i,t_{-i})\in R_i}f_i(t_i\mid t_{-i})\,\varphi_i(t_i\mid t_{-i})^+,
--   $$
--
--   where $x^+=\max\{x,0\}$ and $\varphi_i$ is the ironed conditional virtual value of Definition 7. The left side is the best revenue from a take-it-or-leave-it price for item $i$, offered to the conditional law of $t_i$ given $t_{-i}$, restricted to the types for which $i$ is the favourite item. The identity is what converts the Single term into posted-price revenue in Lemma 6.
--
--   **Formalization Note** The supremum is over real prices. With the $\ge$-tail it is attained (between consecutive values of $t_i$ the revenue $p\cdot\Pr[\cdot]$ increases in $p$, and it is $0$ above the largest), so it equals the maximum of the paper.
--
--   Differences from the source:
--   - correction: max_{p≥max_{j≠i} t_j} p·(1 − F_i(p | t_{−i})) = Σ_{t_i:(t_i,t_{−i})∈R_i} f_i(t_i | t_{−i})·φ_i(t_i | t_{−i})⁺, with 1 − F_i(p | t_{−i}) = Pr[t_i > p | t_{−i}] → sup_{p≥max_{j≠i} t_j} p·Pr[t_i ≥ p ∧ (t_i,t_{−i}) ∈ R_i | t_{−i}] = the same right side; reason: false as printed: n = 2, T = {(1,1)}, i = 1 gives left max_{p≥1} p·Pr[t_1 > p] = 0 and right φ_1(1|1) = 1; the ≥-tail without the region is also false (same instance, i = 2: left 1, right the empty sum 0)
--   - encoding: max_{p≥max_{j≠i} t_j} → supremum over real p ≥ max_{j≠i} t_j; reason: with the ≥-tail, p·Pr[t_i ≥ p ∧ (t_i,t_{−i}) ∈ R_i | t_{−i}] is nondecreasing in p between consecutive values of t_i and 0 above the largest, so the supremum is attained and equals the maximum
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - reading: φ_i(t_i | t_{−i}) ironed over the interval [max_{j≠i} t_j, max Supp(D_{i|t−i})] → ironing (concave majorant of the conditional revenue curve) over the values s with (s, t_{−i}) ∈ T ∩ R_i; reason: R_i is the paper's region for the benchmark; the two sets differ only at s = max_{j≠i} t_j when a smaller index ties, which is not in R_i; checked numerically that Lemma 4 and the Def 7 property hold with this reading
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Definition 7, 'Moreover' property, p.10 (PDF 11)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Definition 7, "Moreover" property, corrected** (Cai & Oikonomou, *On Simple Mechanisms
for Dependent Items*, arXiv:2106.10814v2, p. 10, PDF 11). For any finite type distribution `D`,
item `i` and `t ∈ T`, the best conditional revenue from a take-it-or-leave-it price
`p ≥ max_{j≠i} tⱼ` offered on the favourite region equals the conditional expectation of the
positive part of the ironed virtual value:
`sup_{p ≥ max_{j≠i} tⱼ} p · Pr[tᵢ ≥ p ∧ (tᵢ, t₋ᵢ) ∈ Rᵢ | t₋ᵢ] = Σ_{tᵢ : (tᵢ,t₋ᵢ) ∈ Rᵢ} fᵢ(tᵢ | t₋ᵢ) · φᵢ(tᵢ | t₋ᵢ)⁺`.

**Formalization Note.** The printed left side is `max_{p ≥ max_{j≠i} tⱼ} p · (1 − Fᵢ(p | t₋ᵢ))`
with `1 − Fᵢ(p | t₋ᵢ) = Pr[tᵢ > p | t₋ᵢ]`; it is false as printed (n = 2, T = {(1,1)}, i = 1:
left 0, right 1) and the `≥`-tail repair without the region is false too (same instance, i = 2:
left 1, right 0). The supremum is over real `p`; it is attained (the paper's `max`). The sum ranges over
`regionVals D i t`, the values `s` with `(s, t₋ᵢ) ∈ T ∩ Rᵢ`. -/
theorem definition_7_property {n : ℕ} (D : TypeDist n) (i : Fin n) (t : Fin n → ℝ≥0)
    (ht : t ∈ D.supp) :
    (⨆ p : {p : ℝ // (othersMax i t : ℝ) ≤ p},
        (p : ℝ) * D.condProb i t {u | (p : ℝ) ≤ (u i : ℝ) ∧ Favorite i u}) =
      ∑ s ∈ D.regionVals i t,
        D.cond i (Function.update t i s) * max (D.phi i (Function.update t i s)) 0 := by sorry

end SimpleMechMRF
