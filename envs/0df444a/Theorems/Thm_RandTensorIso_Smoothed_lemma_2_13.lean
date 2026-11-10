-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_2_13
-- name    : RandTensorIso.Smoothed.lemma_2_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:38:13.718191+00:00
-- url     : https://prove2.me/theorems/b63d180f-faa1-4264-9502-0f516766f1ab
-- title:
--   Lemma 2.13 — density of the perturbed tensor in every unitary basis
-- statement:
--   Let $\xi$ be a mean-zero, variance-one sub-Gaussian distribution on $\mathbb C$. Let $M\in\mathbb C^{n\times n\times n}$ have i.i.d. entries $m_{ijk}\sim\xi$, let $t\ge5$, let $\bar M$ have entries $m_{ijk}\mathbf 1\{|m_{ijk}|\le K_\xi\sqrt{t\log n}\}$, and let $F\in\mathbb C^{n\times n\times n}$ satisfy $\|F\|_F\le n^D$ for some $D>0$. Then for $n$ sufficiently large in terms of $K_\xi$, $D$ and $t$, with probability at least $1-n^{-t}$, simultaneously for every $(V_1,V_2,V_3)\in U(n)^3$ the tensor $S=(V_1^*,V_2^*,V_3^*)\curvearrowright(F+\bar M)$ satisfies
--   (i) $|\{p:|S(p)|\ge1/6\}|\ge n^3/(\log n)^2$;
--   (ii) for every $d$ and all $J,K$ with $|J|,|K|\ge n/(4(\log n)^2)$, fewer than $\lceil(\log n)^7\rceil$ indices $x$ satisfy $|S(p)|<1/6$ for every $p\in\mathrm{Rect}_d(x;J,K)$;
--   (iii) for every $d$, $x$ and all $J,K$ with $|J|,|K|\ge n-\lceil(\log n)^7\rceil+1$,
--   $$\sum_{p\in\mathrm{Rect}_d(x;J,K)}|S(p)|^2\ge\frac1{36}.$$
--   In Lean: for $D>0$, $t\ge5$ and $K$ there is $N_0$ such that for every such $\xi$ with $K_\xi=K$, every $n\ge N_0$ and every $F$, the set of $M$ for which some unitary triple violates (i), (ii) or (iii) has (outer) probability at most $n^{-t}$; $\log$ is natural.
--
--   Differences from the source:
--   - reading: for n sufficiently large in terms of K_ξ, D and t → ∃ N₀ chosen from (D, t, K) before ξ, valid for every ξ with K_ξ = K and every n ≥ N₀; reason: the threshold depends only on K_ξ, D, t, so it is uniform over the laws with that K_ξ
--   - reading: with probability at least 1 − n^{-t}, simultaneously for every (V₁, V₂, V₃) → the product measure of {M : some (V₁, V₂, V₃) violates (i), (ii) or (iii)} is ≤ n^{-t}; reason: the event need not be measurable; Lean's measure of a set is its outer measure, which is the stronger reading
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 29 (PDF 31), Lemma 2.13

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_Seed
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian

open MeasureTheory
open scoped Classical

namespace RandTensorIso.Smoothed

/-- Lemma 2.13 (p. 29). For `D > 0`, `t ≥ 5` and `K > 0` there is `N₀` (depending only on
`K_ξ = K`, `D`, `t`) such that for every mean-zero, variance-one sub-Gaussian `ξ` on `ℂ` with
`K_ξ = K`, every `n ≥ N₀` and every `F` with `‖F‖_F ≤ n^D`, the set of `M` for which some
`(V₁, V₂, V₃) ∈ U(n)³` makes `S = (V₁^*, V₂^*, V₃^*) ↷ (F + M̄)` violate (i), (ii) or (iii) has
(outer) probability at most `n^{−t}`; here `M̄` zeroes the entries with `|m_{ijk}| > K_ξ √(t log n)`. -/
theorem lemma_2_13 (D t K : ℝ) (hD : 0 < D) (ht : 5 ≤ t) :
    ∃ N₀ : ℕ, ∀ (ξ : ProbabilityMeasure ℂ), IsStdSubGaussian (ξ : Measure ℂ) →
      subGaussConst (ξ : Measure ℂ) = K →
      ∀ (n : ℕ), N₀ ≤ n → ∀ (F : Tensor3 n), frob F ≤ (n : ℝ) ^ D →
        tensorLaw ξ n {M : Tensor3 n | ∃ V : Fin 3 → U n,
          let Mbar : Tensor3 n := fun p =>
            if ‖M p‖ ≤ K * Real.sqrt (t * Real.log n) then M p else 0
          let S : Tensor3 n := act (star (V 0 : Matrix (Fin n) (Fin n) ℂ))
            (star (V 1 : Matrix (Fin n) (Fin n) ℂ)) (star (V 2 : Matrix (Fin n) (Fin n) ℂ))
            (F + Mbar)
          ¬ (((n : ℝ) ^ 3 / Real.log n ^ 2 ≤
                (Finset.univ.filter (fun p => (1 : ℝ) / 6 ≤ ‖S p‖)).card) ∧
             (∀ (d : Fin 3) (J K' : Finset (Fin n)),
                (n : ℝ) / (4 * Real.log n ^ 2) ≤ J.card →
                (n : ℝ) / (4 * Real.log n ^ 2) ≤ K'.card →
                (Finset.univ.filter (fun x : Fin n =>
                  ∀ a ∈ J, ∀ b ∈ K', ‖S (pos d x a b)‖ < 1 / 6)).card < ⌈Real.log n ^ 7⌉₊) ∧
             (∀ (d : Fin 3) (x : Fin n) (J K' : Finset (Fin n)),
                (n : ℝ) - ⌈Real.log n ^ 7⌉₊ + 1 ≤ J.card →
                (n : ℝ) - ⌈Real.log n ^ 7⌉₊ + 1 ≤ K'.card →
                1 / 36 ≤ rectWeight S d x J K'))} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-t)) := by sorry

end RandTensorIso.Smoothed
