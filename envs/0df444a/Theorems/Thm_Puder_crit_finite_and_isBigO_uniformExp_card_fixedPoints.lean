-- Prove2me | Theorems.Thm_Puder_crit_finite_and_isBigO_uniformExp_card_fixedPoints
-- name    : Puder.crit_finite_and_isBigO_uniformExp_card_fixedPoints
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T09:41:17.715749+00:00
-- url     : https://prove2.me/theorems/84d1262b-79ac-45fc-9d79-2316f03cb101
-- title:
--   Puder, Theorem 2.3 (Puder–Parzanchevski, Thm 1.8) — Crit(w) is finite and E[#fix w(σ)] = 1 + |Crit(w)|/N^{π(w)−1} + O(1/N^{π(w)})
-- statement:
--   Let $d \ge 0$, let $w \in \mathbf F_d$ (`FreeGroup (Fin d)`), and suppose its primitivity rank $\pi(w)$ (`Puder.primitivityRank`) is a finite number $r$. For $N \ge 1$ let $\mathbf E[\mathcal F_{w,N}]$ be the expected number of fixed points of the permutation $w(\sigma_1, \dots, \sigma_d)$ of $\{1, \dots, N\}$, where $\sigma_1, \dots, \sigma_d$ are independent uniformly random permutations: the average, over all $d$-tuples $\sigma$ (`StrongConv.uniformExp`), of the number of points $x$ with $\varphi_\sigma(w)(x) = x$, where $\varphi_\sigma = $ `FreeGroup.lift σ` is the homomorphism $\mathbf F_d \to S_N$ sending the $i$-th generator to $\sigma_i$. Then:
--   1. the set $\mathrm{Crit}(w)$ of $w$-critical subgroups (`Puder.Crit`) is finite;
--   2. as $N \to \infty$,
--   $$\mathbf E[\mathcal F_{w,N}] - 1 - \frac{|\mathrm{Crit}(w)|}{N^{r-1}} = O\Big(\frac{1}{N^{r}}\Big),$$
--   written with Mathlib's `=O[atTop]` over $N \in \mathbb N$; the power $N^{r-1}$ is an integer power (`zpow`), so for $r = 0$ (that is, $w = 1$) the middle term is $|\mathrm{Crit}(w)| \cdot N$.
--
--   The case $\pi(w) = \infty$ (primitive $w$, where the expectation is exactly $1$) is not part of the statement.
--
--   Puder, p. 9: “**Theorem 2.3.** [PP15, Thm 1.8] *For every $w \in \mathbf F_k$, the expected number of fixed points in $w(\sigma_1, \dots, \sigma_k)$ is $$\mathbb E[\mathcal F_{w,n}] = 1 + \frac{|\mathrm{Crit}(w)|}{n^{\pi(w)-1}} + O\Big(\frac{1}{n^{\pi(w)}}\Big).$$* In particular, it is also shown that $\mathrm{Crit}(w)$ is always finite.” Puder's $k$ and $n$ are $d$ and $N$ here. Puder composes permutations from left to right (p. 8, footnote) while `FreeGroup.lift` composes them as functions; the expectation is the same, since $w$ evaluated left to right at $\sigma$ is the inverse of $w$ evaluated as a homomorphism at $(\sigma_1^{-1}, \dots, \sigma_d^{-1})$, a permutation and its inverse have the same fixed points, and $\sigma \mapsto \sigma^{-1}$ preserves the uniform distribution.
--
--   Sources: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 9), citing D. Puder and O. Parzanchevski, *Measure preserving words are primitive*, J. Amer. Math. Soc. 28 (2015) 63–97, https://doi.org/10.1090/S0894-0347-2014-00796-7, Theorem 1.8.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 9, Theorem 2.3, which cites Puder, D. and Parzanchevski, O., Measure preserving words are primitive, J. Amer. Math. Soc. 28 (2015) 63–97, https://doi.org/10.1090/S0894-0347-2014-00796-7, Theorem 1.8

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Asymptotics Filter

namespace Puder

theorem crit_finite_and_isBigO_uniformExp_card_fixedPoints (d : ℕ) (w : FreeGroup (Fin d)) (r : ℕ)
    (hr : primitivityRank w = r) :
    (Crit w).Finite ∧
      (fun N : ℕ => StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ)) - 1 -
          ((Crit w).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1)) =O[atTop]
        (fun N : ℕ => 1 / (N : ℝ) ^ r) := by
  sorry

end Puder
