-- Prove2me | Theorems.Thm_TaoFivePrimes_vaughan_identity_interface
-- name    : TaoFivePrimes.vaughan_identity_interface
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T09:23:44.986631+00:00
-- url     : https://prove2.me/theorems/65e8532a-0b76-404a-9c31-24cd56bec293
-- title:
--   Vaughan's identity in the Type I interface vocabulary
-- statement:
--   ## Vaughan's identity in the interface vocabulary
--
--   For integers $U,V\ge0$, the platform's restricted Möbius and von Mangoldt functions satisfy
--   $$\mu_{\le U}*\log-\mu_{\le U}*\Lambda_{\le V}*\zeta+\mu_{>U}*\Lambda_{>V}*\zeta+\Lambda_{\le V}=\Lambda .$$
--   This is Vaughan's identity in the form used by Tao's Lemma 4.11 in the `arithmeticRestrictLE`/`arithmeticRestrictGT` vocabulary of the Type I interface: the first three terms are exactly the Type I part `vaughanTypeIPart` with its third term written as $\mu_{>U}*(\Lambda_{>V}*\zeta)$ instead of the centred half-logarithm $\mu_{>U}*(\tfrac12\log)_{>V}$, and the closing term $\Lambda_{\le V}$ is invisible against any test function supported above $V$.
--
--   The proof is the standard one: $\log=\Lambda*\zeta$ and $\mu*\zeta=1$, so $\Lambda=\mu*\log$; splitting $\mu=\mu_{\le U}+\mu_{>U}$ and $\Lambda=\Lambda_{\le V}+\Lambda_{>V}$ and rearranging the Dirichlet products gives the identity.
-- source:
--   Terence Tao, arXiv:1201.6656v4, Lemma 4.11 (Vaughan's identity), in the restricted-arithmetic-function vocabulary of Definition TaoFivePrimes_TypeIEnvelopeInterfaces.

import Mathlib
import Theorems.Thm_TaoFivePrimes_typeIExpansion_three_bilinear_sums

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius BigOperators
open ArithmeticFunction Finset

theorem TaoFivePrimes.vaughan_identity_interface (U V : ℕ) :
    TaoFivePrimes.arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
      - TaoFivePrimes.arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) *
          TaoFivePrimes.arithmeticRestrictLE V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      + TaoFivePrimes.arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) *
          TaoFivePrimes.arithmeticRestrictGT V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      + TaoFivePrimes.arithmeticRestrictLE V ArithmeticFunction.vonMangoldt
      = ArithmeticFunction.vonMangoldt := by sorry
