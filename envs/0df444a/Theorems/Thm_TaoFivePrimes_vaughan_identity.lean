-- Prove2me | Theorems.Thm_TaoFivePrimes_vaughan_identity
-- name    : TaoFivePrimes.vaughan_identity
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T16:14:49.309286+00:00
-- url     : https://prove2.me/theorems/b1b8cb46-73ff-40c6-8165-b429daf56951
-- title:
--   Vaughan's identity: $\Lambda = \mu\mathbf 1_{\le U} * \log - \mu\mathbf 1_{\le U} * \Lambda\mathbf 1_{\le V} * \zeta + \mu\mathbf 1_{>U} * \Lambda\mathbf 1_{>V} * \zeta + \Lambda\mathbf 1_{\le V}$
-- statement:
--   Work in the ring of real-valued arithmetic functions under Dirichlet convolution, writing $*$ for the convolution, $\zeta$ for the constant-one function, $\mu$ for the Möbius function, $\Lambda$ for the von Mangoldt function and $\log$ for $n\mapsto\log n$. For real cutoffs $U,V$ let $f\mathbf 1_{\le U}$ and $f\mathbf 1_{>U}$ denote the truncations of an arithmetic function $f$ to arguments at most $U$, respectively greater than $U$. Then
--
--   $$\Lambda\;=\;\mu\mathbf 1_{\le U}*\log\;-\;\mu\mathbf 1_{\le U}*\Lambda\mathbf 1_{\le V}*\zeta\;+\;\mu\mathbf 1_{>U}*\Lambda\mathbf 1_{>V}*\zeta\;+\;\Lambda\mathbf 1_{\le V}.$$
--
--   This is Vaughan's identity in the exact form used to open the minor-arc analysis. Read pointwise at an integer $n$ and summed against a test function, the first two terms become Type I sums, in which one variable runs over a short range and the other carries a smooth weight; the third is the genuinely bilinear Type II sum handled by the large sieve; and the fourth is supported on $n\le V$ and is negligible for the test functions used, which vanish there.
--
--   **Formalization Note** The truncations and the Dirichlet convolution are those of the ambient library; the constant-one function and the Möbius function are taken with real values so that all four terms live in the same ring.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.11 ("A variant of Vaughan's identity"), the displayed identity in its proof, labelled (vaughan) in the arXiv source: "Lambda = mu*1_{<=U} * Lambda * 1 - mu*1_{<=U} * Lambda*1_{<=V} * 1 + mu*1_{>U} * Lambda*1_{>V} * 1 + mu * Lambda*1_{<=V} * 1 = mu*1_{<=U} * log - mu*1_{<=U} * Lambda*1_{<=V} * 1 + mu*1_{>U} * Lambda*1_{>V} * 1 + Lambda*1_{<=V}". Originally R. C. Vaughan, Sommes trigonometriques sur les nombres premiers, C.R. Acad. Sci. Paris 285 (1977), 981-983.

import Mathlib
import Definitions.Def_TaoFivePrimes_VaughanTruncation

theorem TaoFivePrimes.vaughan_identity (U V : ℝ) :
    TaoFivePrimes.truncLe U TaoFivePrimes.moebiusR * ArithmeticFunction.log
      - TaoFivePrimes.truncLe U TaoFivePrimes.moebiusR *
          TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt * TaoFivePrimes.zetaR
      + TaoFivePrimes.truncGt U TaoFivePrimes.moebiusR *
          TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * TaoFivePrimes.zetaR
      + TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt
      = ArithmeticFunction.vonMangoldt := by sorry
