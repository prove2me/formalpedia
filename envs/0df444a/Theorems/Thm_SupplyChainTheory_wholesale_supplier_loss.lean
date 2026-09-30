-- Prove2me | Theorems.Thm_SupplyChainTheory_wholesale_supplier_loss
-- name    : SupplyChainTheory.wholesale_supplier_loss
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:26:22.61589+00:00
-- url     : https://prove2.me/theorems/09be8cb6-d273-4594-b38a-13d7056ef123
-- title:
--   Theorem 14.1 (second part): at the coordinating wholesale price the supplier's expected profit is negative
-- statement:
--   **Theorem 14.1, second part.** At the wholesale price $w = c_s - \frac{c - v}{r - v + p}p_s$ of
--   (14.13) and the supply-chain-optimal quantity $Q_0$, the supplier's expected profit
--   $\pi_s(Q_0, w) = p_s S(Q_0) + (w - c_s)Q_0 - p_s\mu$ is negative.
--
--   Since $v < c$ and $r > c$ the coefficient of $p_s$ in (14.13) is negative, so $w < c_s$ when
--   $p_s > 0$; with $S(Q_0) \le \mu$ and $Q_0 > 0$ every term is nonpositive and the margin term
--   is strictly negative. (The book's last sentence says "the retailer" where it means the
--   supplier, as the theorem statement does.) This is why the wholesale price contract is not a
--   coordinating contract: the only coordinating price is one the supplier would not accept.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 569-570, Sect. 14.5, Theorem 14.1 ('Moreover, the supplier earns a negative expected profit under this wholesale price') and the end of its proof

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_supplier_loss (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D)
    (hps : 0 < P.ps) (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - ProbabilityTheory.cdf D 0)
    (Q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) :
    supplierProfit P D (wholesaleTransfer (wholesaleCoordPrice P)) Q0 < 0 := by sorry

end SupplyChainTheory
