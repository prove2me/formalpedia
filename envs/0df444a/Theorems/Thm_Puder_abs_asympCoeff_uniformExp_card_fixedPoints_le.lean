-- Prove2me | Theorems.Thm_Puder_abs_asympCoeff_uniformExp_card_fixedPoints_le
-- name    : Puder.abs_asympCoeff_uniformExp_card_fixedPoints_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T09:41:17.35877+00:00
-- url     : https://prove2.me/theorems/6ace050e-b96c-42e4-b40b-bcfc2b6c9092
-- title:
--   Puder, §5.5 (proof of Proposition 5.1) — |a_s(w)| ≤ t^{2s+2} for s ≥ π(w), for w ≠ 1 of reduced length t
-- statement:
--   Let $d \ge 0$ and let $1 \ne w \in \mathbf F_d$ (`FreeGroup (Fin d)`) have reduced length $t$ (`w.toWord.length`). Let $a_s(w)$ be the coefficients of the expansion of the expected number of fixed points of $w(\sigma_1, \dots, \sigma_d)$ in powers of $1/N$,
--   $$\mathbf E[\mathcal F_{w,N}] = \sum_{s \ge 0} \frac{a_s(w)}{N^s},$$
--   taken as `StrongConv.asympCoeff` of the function $N \mapsto \mathbf E[\mathcal F_{w,N}]$; here $\mathbf E[\mathcal F_{w,N}]$ is the average, over all $d$-tuples $\sigma$ of permutations of $\{1, \dots, N\}$ (`StrongConv.uniformExp`), of the number of fixed points of `FreeGroup.lift σ w`. Then for every $s$ with $s \ge \pi(w)$ (`Puder.primitivityRank`),
--   $$|a_s(w)| \le t^{2(s+1)}.$$
--
--   Puder, pp. 28–29, proof of Proposition 5.1 (stated there for reduced words: “Note that we pass here to reduced words”): “This expression can be expressed as a Taylor series in $\frac1n$, so write $$\mathbb E[\mathcal F_{w,n}] = \sum_{s=0}^\infty \frac{a_s(w)}{n^s}$$ … So our goal here is to bound the remaining coefficients $a_s(w)$ for $s \ge \pi(w)$.” and, after the Claim $|P_{M,q}| \le t^{2q}$, “Hence from (5.9) we obtain, $$|a_s(w)| \le \sum_{i=1}^{s+1} \binom{t}{2}^{i} t^{2(s-(i-1))} \le \sum_{i=1}^{s+1} \frac{t^{2i}}{2^i} \cdot t^{2(s-i+1)} \le t^{2s+2}.$$” Puder's $k$ and $n$ are $d$ and $N$ here, and Puder composes permutations from left to right, which does not change the expected number of fixed points (a permutation and its inverse have the same fixed points, and inverting each $\sigma_i$ preserves the uniform distribution). The hypothesis $w \ne 1$ is Proposition 5.1's “$\pi(w) \ne 0$ (so $w$ does not reduce to 1)”.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, §5.5, pp. 28–29).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), pp. 28–29, §5.5, proof of Proposition 5.1 (the bound on a_s(w))

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

namespace Puder

theorem abs_asympCoeff_uniformExp_card_fixedPoints_le (d : ℕ) (w : FreeGroup (Fin d)) (hw : w ≠ 1)
    (s : ℕ) (hs : primitivityRank w ≤ s) :
    |StrongConv.asympCoeff (fun N : ℕ => StrongConv.uniformExp
        (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ))) s| ≤
      (w.toWord.length : ℝ) ^ (2 * (s + 1)) := by
  sorry

end Puder
