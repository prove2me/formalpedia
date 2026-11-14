-- Prove2me | Theorems.Thm_ProxGapTight_adsw20_cor_2_2_7_plane
-- name    : ProxGapTight.adsw20_cor_2_2_7_plane
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T22:43:17.478692+00:00
-- url     : https://prove2.me/theorems/8d2df70c-54dd-4715-984e-34452861ca90
-- title:
--   ADSW20 Corollary 2.2.7 — small words of the points–lines code of PG(2, q) are combinations of at most two (weight ≤ 3q−4) or at most three lines, or of Bagchi's type (weight ≤ 4q−22)
-- statement:
--   Adriaensen, Denaux, Storme and Weiner (arXiv v2, p. 4) state: "Corollary 2.2.7. Let $c$ be a code word of $C_1(2,q)$, with $q = p^h$, $p$ prime, and $q \notin \{8, 9, 16, 25, 27, 49\}$. • If $\mathrm{wt}(c) \leqslant 3q - 4$, then $c$ is a linear combination of at most two lines. • If $\mathrm{wt}(c) \leqslant 3q + 1$ and $q = 121$, then $c$ is a linear combination of at most three lines. • If $\mathrm{wt}(c) \leqslant \max\{3q + 1, 4q - 22\}$ and $q > 17$, $q \neq 121$, then $c$ is a linear combination of at most three lines or given by Example 2.2.3." Here $C_1(2,q)$ is the $p$-ary code spanned by the incidence vectors of the lines of $\mathrm{PG}(2,q)$, indexed by the points. The corollary collects Bagchi's theorem (prime $q$, weight below $3p-3$) and Szőnyi–Weiner's Theorems 4.3, 4.8 and Corollary 4.10.
--
--   **Statement.** Let $p$ be prime and $q = p^a$ with $q > 32$, $q \ne 49$, $q \ne 121$, and let $K$ be a field with $q$ elements. Points of $\mathrm{PG}(2, q)$ are the lines (one-dimensional subspaces, `ProxGapTight.Lines K 3`) of $K^3$, and lines of $\mathrm{PG}(2,q)$ are the two-dimensional subspaces $H$; $\mathbf 1_H$ is the $\mathbb F_p$-valued indicator of the points contained in $H$. Let $v$ be in the $\mathbb F_p$-span of the $\mathbf 1_H$ and let $\mathrm{wt}(v)$ be the number of points where $v \ne 0$. Then:
--   1. if $\mathrm{wt}(v) \le 3q - 4$, then $v = \alpha \mathbf 1_H + \beta \mathbf 1_{H'}$ for some lines $H, H'$ and $\alpha, \beta \in \mathbb F_p$;
--   2. if $\mathrm{wt}(v) \le 4q - 22$, then either $v = \alpha \mathbf 1_{H_1} + \beta \mathbf 1_{H_2} + \gamma \mathbf 1_{H_3}$ for some lines $H_i$ and $\alpha, \beta, \gamma \in \mathbb F_p$, or $q$ is prime ($a = 1$) and there are a point $S$ and three distinct lines $H_1, H_2, H_3$ through $S$ such that every point where $v \ne 0$ lies on one of them and, on each $H_i$, $v$ takes pairwise distinct values at the $q$ points other than $S$.
--
--   Lines may coincide and coefficients may be zero in the combinations, so $v = 0$ and combinations of fewer lines are included. For $q > 32$ the third bullet's bound $\max\{3q+1, 4q-22\}$ is $4q - 22$; the second bullet ($q = 121$) is not formalized, and the first and third are stated for $q > 32$ only.
--
--   **Formalization note.** The second alternative of item 2 is a property of the code words of Example 2.2.3, not their definition. Those code words are the images under a collineation of $\gamma c + \lambda m + \lambda' m' + \lambda'' m''$ ($\gamma \ne 0$), where $m, m', m''$ are the concurrent lines $X_0 = 0$, $X_1 = 0$, $X_0 = X_1$ of $\mathrm{PG}(2,p)$ and $c$ is Example 2.2.2's word. That word is $a$ at $(0,1,a)$, $b$ at $(1,0,b)$, $-c$ at $(1,1,c)$ and $0$ elsewhere. On $m$ minus the common point $(0,0,1)$ such a word takes the values $\gamma a + \lambda$, $a \in \mathbb F_p$, which are pairwise distinct, and likewise on $m'$ and $m''$; its support lies on $m \cup m' \cup m''$. So the statement is implied by the corollary. It was published so that `ProxGapTight.ad21_result_3_3_hyperplanes` can be reduced to it.
-- source:
--   S. Adriaensen, L. Denaux, L. Storme, Zs. Weiner, Small weight code words arising from the incidence of points and hyperplanes in PG(n, q), Des. Codes Cryptogr. 88 (2020) 771–788, https://doi.org/10.1007/s10623-019-00710-0 (arXiv:1905.04978v2), p. 4, Corollary 2.2.7 (arXiv v2 numbering), summarising B. Bagchi, arXiv:1712.07391, Thm 1.1, and T. Szőnyi, Zs. Weiner, J. Combin. Theory Ser. A 157 (2018) 321–333, https://doi.org/10.1016/j.jcta.2018.02.005, Thms 4.3, 4.8 and Cor. 4.10

import Mathlib
import Definitions.Def_ProxGapTight_Lines

namespace ProxGapTight

theorem adsw20_cor_2_2_7_plane (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (v : Lines K 3 → ZMod p)
    (hv : v ∈ Submodule.span (ZMod p) (Set.range fun H :
        {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3} =>
          Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p)))) :
    (hammingNorm v ≤ 3 * p ^ a - 4 →
      ∃ H H' : {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3}, ∃ α β : ZMod p,
        v = α • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p)) +
          β • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H'.1} (fun _ => (1 : ZMod p))) ∧
    (hammingNorm v ≤ 4 * p ^ a - 22 →
      (∃ H₁ H₂ H₃ : {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3},
        ∃ α β γ : ZMod p,
          v = α • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H₁.1} (fun _ => (1 : ZMod p)) +
            β • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H₂.1} (fun _ => (1 : ZMod p)) +
            γ • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H₃.1} (fun _ => (1 : ZMod p))) ∨
      (a = 1 ∧ ∃ S : Lines K 3,
        ∃ H₁ H₂ H₃ : {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3},
          S.1 ≤ H₁.1 ∧ S.1 ≤ H₂.1 ∧ S.1 ≤ H₃.1 ∧ H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
          (∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ H₁.1 ∨ ℓ.1 ≤ H₂.1 ∨ ℓ.1 ≤ H₃.1) ∧
          ∀ H ∈ ({H₁, H₂, H₃} : Set {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3}),
            ∀ ℓ ℓ' : Lines K 3, ℓ.1 ≤ H.1 → ℓ'.1 ≤ H.1 → ℓ ≠ S → ℓ' ≠ S → v ℓ = v ℓ' → ℓ = ℓ')) := by
  sorry

end ProxGapTight
