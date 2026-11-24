-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0VaughanBilinearSum_eq_centredPairSum
-- name    : TaoFivePrimes.eta0VaughanBilinearSum_eq_centredPairSum
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T08:12:45.930345+00:00
-- url     : https://prove2.me/theorems/f579af0d-daec-4123-94db-92a652395d6c
-- title:
--   The bilinear sum is the centred pair sum
-- statement:
--   ## The platform bilinear sum is the centred pair sum
--
--   Let $x,\alpha\in\mathbb R$ and $U,V\ge 40$ with $U,V<x$, $UV\le x/4$, $x\le UV^2$. Then the platform's bilinear sum `TaoFivePrimes.eta0VaughanBilinearSum` equals the explicit centred pair sum
--
--   $$\sum_{d\ge 1}\sum_{w\ge 1}\mu(d)\,\mathbf 1_{U<d}\,\mathbf 1_{V<w}\,\mathbf 1_{(d,2)=(w,2)=1}\;g(w)\;\eta_0(dw/x)\,e(\alpha dw),\qquad g(w)=\sum_{\substack{b\mid w\\ b>V}}\Lambda(b)-\tfrac12\log w .$$
--
--   Indeed `TaoFivePrimes.eta0VaughanBilinearSum` pairs $\bigl(\mathrm{trunc}_{>\lfloor U\rfloor}\mu\bigr)(p_1)$ with the coefficient $\mathrm{trunc}_{>\lfloor V\rfloor}\Lambda*\zeta-\tfrac12\log(\cdot)\mathbf 1_{>\lfloor V\rfloor}$ of `TaoFivePrimes.vaughanTypeIICoefficient`, tested against $\eta_0(p_1p_2/x)e(\alpha p_1p_2)$ over pairs $p_1p_2\le\lfloor x\rfloor$; the conditions $p_1p_2\le\lfloor x\rfloor$ and $p_1p_2\le x$ agree for integer products, the coprimality test restricts to odd $p_1,p_2$, and for integer $b,w$ the conditions $b>V$ and $b>\lfloor V\rfloor$ agree, so the divisor coefficient is exactly $g(w)$ on the odd pairs that survive. This is the coefficient identity at the heart of the centring step of Tao's Lemma 4.11, isolated as a reindexing statement.
-- source:
--   Terence Tao, arXiv:1201.6656v4, Section 4, Lemma 4.11: the centring of the Type II divisor coefficient by $-\tfrac12\log w$; statement of the identification between the platform bilinear sum and the explicit centred pair sum.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIIChunkInterfaces

theorem TaoFivePrimes.eta0VaughanBilinearSum_eq_centredPairSum
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.eta0VaughanBilinearSum x alpha U V =
      ∑' d : ℕ, ∑' w : ℕ,
          (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
              TaoFivePrimes.expCircle (alpha * d * w) *
              ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
          else 0) := by sorry
