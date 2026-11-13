-- Prove2me | Theorems.Thm_ProxGapTight_ad21_result_3_3_hyperplanes
-- name    : ProxGapTight.ad21_result_3_3_hyperplanes
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T18:08:47.151205+00:00
-- url     : https://prove2.me/theorems/bee7d213-b038-4a60-ae60-2f498ed81ef8
-- title:
--   AD21 Result 3.3 — small words of the points–hyperplanes code of PG(d−1, q) are combinations of at most two hyperplanes
-- statement:
--   Adriaensen and Denaux (arXiv v1, p. 4) state: "Result 3.3 ([ADSW20, Corollary 2.2.13] [PZ18, Theorem 1.4]). If $c$ is a code word of $C_k(k+1, q)$, with $\mathrm{wt}(c) \leqslant W(k, q)$, then $c$ is a linear combination of at most two $k$-spaces." Here $C_k(k+1,q)$ is the $p$-ary code spanned by the incidence vectors of the hyperplanes ($k$-spaces) of $\mathrm{PG}(k+1, q)$, indexed by the points. This statement formalizes it at the cutoff $3q^k - 3q^{k-1} - 1$, the value of $W(k,q)$ for prime $q > 32$ (their class $Q_3$). For $q > 32$ even ($Q_4$) and for the other $q > 32$ outside $\{49, 121\}$ ($Q_5$), $W(k,q)$ is larger, so the statement is a weakening of Result 3.3 there.
--
--   **Statement.** Let $p$ be prime and $q = p^a$ with $q > 32$, $q \ne 49$, $q \ne 121$. Let $d \ge 3$ and let $K$ be a field with $q$ elements. Points of $\mathrm{PG}(d-1, q)$ are the lines (one-dimensional subspaces, `ProxGapTight.Lines K d`) of $K^d$, and hyperplanes are the subspaces of dimension $d - 1$. For a hyperplane $H$, $\mathbf 1_H$ is the $\mathbb F_p$-valued indicator of the lines contained in $H$. If $v$ is in the $\mathbb F_p$-span of the $\mathbf 1_H$ and at most $3q^{d-2} - 3q^{d-3} - 1$ lines carry a nonzero value of $v$, then $v = \alpha \mathbf 1_H + \beta \mathbf 1_{H'}$ for some hyperplanes $H, H'$ and $\alpha, \beta \in \mathbb F_p$. Here $k = d - 2$. $H = H'$ and zero coefficients are allowed, so $v = 0$ and single hyperplanes are included.
--
--   It was published so that `ProxGapTight.theorem_3_3_small_weight` (Kominers–Thaler–Zheng's Theorem 3.3, cited there from [AD21, Theorem 5.9]) can be reduced to it: the reduction formalizes AD21's induction step (Lemmas 5.2, 5.4, 5.6–5.8 and Theorem 5.9) for codimension-two subspaces, from this base case.
-- source:
--   S. Adriaensen, L. Denaux, Small weight codewords of projective geometric codes, J. Combin. Theory Ser. A 180 (2021) 105395, https://doi.org/10.1016/j.jcta.2020.105395 (arXiv:2003.10337), p. 4, Result 3.3 (arXiv v1 numbering), citing S. Adriaensen, L. Denaux, L. Storme, Zs. Weiner, Des. Codes Cryptogr. 88 (2020) 771–788, https://doi.org/10.1007/s10623-019-00710-0, Cor. 2.2.13, and O. Polverino, F. Zullo, J. Combin. Theory Ser. A 158 (2018) 1–11, https://doi.org/10.1016/j.jcta.2018.03.013, Thm 1.4

import Mathlib
import Definitions.Def_ProxGapTight_Lines

namespace ProxGapTight

theorem ad21_result_3_3_hyperplanes (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) (d : ℕ) (hd : 3 ≤ d)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (v : Lines K d → ZMod p)
    (hv : v ∈ Submodule.span (ZMod p) (Set.range fun H :
        {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d} =>
          Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p))))
    (hw : hammingNorm v ≤ 3 * (p ^ a) ^ (d - 2) - 3 * (p ^ a) ^ (d - 3) - 1) :
    ∃ H H' : {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d}, ∃ α β : ZMod p,
      v = α • Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p)) +
        β • Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H'.1} (fun _ => (1 : ZMod p)) := by
  sorry

end ProxGapTight
