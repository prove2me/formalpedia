-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_generic_rank_le_binary
-- name    : ParityDegreeDepth.Core.generic_rank_le_binary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:25.2258+00:00
-- url     : https://prove2.me/theorems/ca1561d1-33c3-5b7c-842b-bd8b27cdf27a
-- title:
--   Lemma 3.3 (multi-affine form): generic rank $\le 2^k\cdot$ binary rank
-- statement:
--   Let $D$ be an integral domain, $k,n\ge0$, and for every $g:[k]\to[n]$ let $N_g$ be an $m\times r$ matrix over $D$. Form the matrix which is multilinear in $k$ blocks of $n$ indeterminates $t_\ell=(t_{\ell,1},\dots,t_{\ell,n})$,
--
--   $$
--   N(t)\;=\;\sum_{g:[k]\to[n]}\Big(\prod_{\ell=1}^{k} t_{\ell,g(\ell)}\Big)\,N_g ,
--   $$
--
--   and for an assignment $a$ of the variables write $N(a)=\sum_g\big(\prod_\ell a_{\ell,g(\ell)}\big)N_g$. Then there is a binary assignment $a\in\{0,1\}^{k\times n}$ with
--
--   $$
--   \operatorname{rank}_{\operatorname{Frac}D[t]} N(t)\;\le\;2^k\,\operatorname{rank}_{\operatorname{Frac}D} N(a).
--   $$
--
--   For $D=\mathbb F_2$ this is Lemma 3.3: the generic rank $R(N)$ is at most $2^k M(N)$, where $M(N)$ is the largest rank at a binary point. It is used with the generic contraction $T(t_1,\dots,t_{d-2},-,-)$ to obtain $R\le 2^{d-2}M(T)$ (Corollary 3.4).
--
--   **Formalization Note** Every matrix which is multilinear in the $k$ blocks (each entry homogeneous of degree one in each block) has this form. Ranks are taken over fraction fields, i.e. generic rank.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §3.3, Lemma 3.3 (citing Moshkovitz-Zhu, Theorem 1.1) and its proof in Appendix B.2 (multi-affine matrices over arbitrary fields/domains, multiplicity grid inequality Lemma B.3), pp. 6, 23

import Mathlib

theorem ParityDegreeDepth.Core.generic_rank_le_binary (k : ℕ) (D : Type) [CommRing D] [IsDomain D]
    {n m r : ℕ} (N : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D) :
    ∃ a : Fin k × Fin n → D, (∀ q, a q = 0 ∨ a q = 1) ∧
      ((∑ g : Fin k → Fin n, (∏ l, (MvPolynomial.X (l, g l) : MvPolynomial (Fin k × Fin n) D)) •
          (N g).map (MvPolynomial.C : D →+* MvPolynomial (Fin k × Fin n) D)).map
          (algebraMap (MvPolynomial (Fin k × Fin n) D)
            (FractionRing (MvPolynomial (Fin k × Fin n) D)))).rank ≤
        2 ^ k * ((∑ g : Fin k → Fin n, (∏ l, a (l, g l)) • N g).map
          (algebraMap D (FractionRing D))).rank := by sorry
