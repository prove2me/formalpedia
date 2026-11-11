-- Prove2me | Theorems.Thm_RobustKZClust_Main_lemma_3_1
-- name    : RobustKZClust.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:12:34.360255+00:00
-- url     : https://prove2.me/theorems/a825ab1d-baec-4fcc-9c16-2974f8eda197
-- title:
--   Lemma 3.1 — averaged projections from a short seed preserve dist(x, C)^z for all x, C ⊆ X at once
-- statement:
--   **Robust dimensionality reduction.** There are absolute constants $c_1,K_0$ such that for every $\delta_0\in(0,1)$ there is $C_0>0$ with the following property. Let $\varepsilon\in(0,1)$, let $z,k\ge1$ and $d$ be integers, and let $X\subseteq\mathbb R^d$ be finite. Then there are dimensions
--   $$1\le\tilde d\le C_0\bigl(z\varepsilon^{-1}\log_2(k+2)\bigr)^{c_1},\qquad 1\le n_g\le\bigl(C_0\,z\varepsilon^{-1}k\log_2(|X|+2)\bigr)^{c_1z}$$
--   and two programs of the mission's machine, each with at most $K_0$ real registers. The **seed program** uses coins and leaves a seed in memory. The **entry program** is deterministic: on input $(j,r,c)$ and the seed, it returns the entry $(G_j)_{r,c}$ of a matrix $G_j\in\mathbb R^{\tilde d\times d}$ in real register $0$. Both always halt. At every step of either call the memory has at most
--   $$C_0\,z\,k\,\log_2(|X|+2)\,\log_2\!\bigl(2+\varepsilon^{-1}zkd\log_2(|X|+2)\bigr)\ \text{bits}.$$
--   With probability at least $1-\delta_0$ over the coins of the seed call, for every $x\in X$ and every nonempty $C\subseteq X$ with $|C|\le k$,
--   $$(1-\varepsilon)\,\mathrm{dist}(x,C)^z\le\frac1{n_g}\sum_{j=1}^{n_g}\mathrm{dist}(G_jx,G_jC)^z\le(1+\varepsilon)\,\mathrm{dist}(x,C)^z.\qquad(17)$$
--
--   Because the guarantee holds for all pairs $(x,C)$ in the ground set at once, an adaptive adversary cannot find a pair on which the projections fail. The main algorithm applies it with the finite universal domain $X_\varepsilon$.
--
--   **Formalization Note.** The failure event is bounded in outer measure under the fair-tape law.
--
--   Differences from the source:
--   - reading: "can be computed from a shared random seed using O(zk log|X| log(ε⁻¹zkd log|X|)) space" → a seed call with coins and a deterministic entry-evaluation call on the mission's machine, with that bit space at every step of both calls; reason: the paper names no machine (§2).
--   - reading: "with high constant probability" → for every δ₀ ∈ (0, 1), with C₀ depending on δ₀ and exponents absolute; reason: strongest reading of a constant success probability.
--   - reading: d̃ := poly(zε⁻¹ log k), n_g := (zε⁻¹k log|X|)^{O(z)} → existential d̃, n_g ≥ 1 bounded by C₀(zε⁻¹ log₂(k+2))^{c₁} and (C₀zε⁻¹k log₂(|X|+2))^{c₁z}; reason: explicit constants for poly and O; log₂(·+2) avoids the degenerate value log 1 = 0 at k = 1 or |X| = 1.
--   - reading: C ⊆ X with |C| ≤ k → nonempty C; reason: dist(x, ∅) is undefined.
--   - encoding: = (1 ± ε) dist(x, C)^z → the two-sided inequality; reason: notation.
--   - reading: log |X| in the space bound O(zk log|X| log(ε⁻¹zkd log|X|)) → log₂(|X|+2); reason: as for n_g, avoids the degenerate value log 1 = 0 at |X| = 1.
--   - encoding: the ground set X ⊆ R^d, and k → a finite set (Finset), and k ≥ 1; reason: |X| and log k presuppose a finite X and k ≥ 1.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 13, Lemma 3.1, Eq. (17)

import Mathlib
import Definitions.Def_RobustKZClust_Main_Cost
import Definitions.Def_RobustKZClust_Main_Machine
import Definitions.Def_RobustKZClust_Main_Proj

namespace RobustKZClust.Main

/-- Lemma 3.1 (p. 13): robust dimension reduction. A seed call (with coins) stores a seed; a
deterministic entry call on the integer input `(j, r, c)` returns the entry `(G_j)_{r,c}` in real
register `0`. Dimensions `d̃ = poly(z ε⁻¹ log k)`, `n_g = (z ε⁻¹ k log |X|)^{O(z)}`, bit space
`O(z k log |X| · log(ε⁻¹ z k d log |X|))`, and with probability `≥ 1 − δ₀` over the coins the
averaged projections preserve `dist(x, C)^z` within `1 ± ε` for all `x ∈ X`, nonempty `C ⊆ X`,
`|C| ≤ k` (17). -/
theorem lemma_3_1 :
    ∃ c₁ K₀ : ℕ, ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (z k d : ℕ), 1 ≤ z → 1 ≤ k → ∀ X : Finset (Pt d),
      ∃ (dt ng : ℕ), 1 ≤ dt ∧
        (dt : ℝ) ≤ C₀ * ((z : ℝ) / ε * Real.logb 2 (k + 2)) ^ c₁ ∧
        1 ≤ ng ∧
        (ng : ℝ) ≤ (C₀ * (z : ℝ) / ε * k * Real.logb 2 (X.card + 2)) ^ (c₁ * z) ∧
      ∃ (Pseed Pent : Program),
        RegsBelow Pseed K₀ ∧ RegsBelow Pent K₀ ∧ Deterministic Pent ∧
        (∀ ω : ℕ → Bool, ∃ s, Halted Pseed (callRun Pseed ω ⟨[], []⟩ zeroMem s)) ∧
        (∀ (ω : ℕ → Bool) (j : Fin ng) (r : Fin dt) (c : Fin d), ∃ s,
          Halted Pent (callRun Pent blankTape ⟨[(j : ℤ), (r : ℤ), (c : ℤ)], []⟩
            (callFinal Pseed ω ⟨[], []⟩ zeroMem).mem s)) ∧
        (let B : ℝ := C₀ * z * k * Real.logb 2 (X.card + 2) *
            Real.logb 2 (2 + (z : ℝ) * k * d * Real.logb 2 (X.card + 2) / ε)
         (∀ (ω : ℕ → Bool) (s : ℕ), SpaceLE (callRun Pseed ω ⟨[], []⟩ zeroMem s).mem B) ∧
         ∀ (ω : ℕ → Bool) (j : Fin ng) (r : Fin dt) (c : Fin d) (s : ℕ),
           SpaceLE (callRun Pent blankTape ⟨[(j : ℤ), (r : ℤ), (c : ℤ)], []⟩
             (callFinal Pseed ω ⟨[], []⟩ zeroMem).mem s).mem B) ∧
        (let G : (ℕ → Bool) → Fin ng → Matrix (Fin dt) (Fin d) ℝ := fun ω j r c =>
            (callFinal Pent blankTape ⟨[(j : ℤ), (r : ℤ), (c : ℤ)], []⟩
              (callFinal Pseed ω ⟨[], []⟩ zeroMem).mem).reg 0
         tapeMeasure {ω | ¬ ∀ x ∈ X, ∀ C : Finset (Pt d), C ⊆ X → C.Nonempty → C.card ≤ k →
            (1 - ε) * distSet x C ^ z ≤
              (1 / (ng : ℝ)) * ∑ j, distSet (applyMat (G ω j) x) (applyMatSet (G ω j) C) ^ z ∧
            (1 / (ng : ℝ)) * ∑ j, distSet (applyMat (G ω j) x) (applyMatSet (G ω j) C) ^ z ≤
              (1 + ε) * distSet x C ^ z} ≤ ENNReal.ofReal δ₀) := by sorry

end RobustKZClust.Main
