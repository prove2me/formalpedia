-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_tight_ratio_limit
-- name    : ProcurementPoA.DeterministicCap.Supplement.tight_ratio_limit
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:31:03.339472+00:00
-- url     : https://prove2.me/theorems/87576fb3-64c4-4329-8cfc-9c5649d5e111
-- title:
--   Remark 4.2 — exact limiting cost ratio after value-to-cost transformation
-- statement:
--   Fix real costs $0<L\le U$ and put $\varepsilon=e^{-2}$. Suppose that two real sequences $o_k$ and $w_k$ satisfy $o_k\to1$ and $w_k\to1-\varepsilon$. Then
--   $$
--   \frac{U-(U-L)w_k}{U-(U-L)o_k}
--   \longrightarrow 1+\varepsilon\left(\frac UL-1\right).
--   $$
--   This is the exact limit calculation in Remark 4.2. Here $o_k$ represents optimal value welfare and $w_k$ equilibrium value welfare; the displayed numerator and denominator are respectively expected equilibrium and optimal procurement cost under $c=U-(U-L)v$. The calculation also covers the degenerate interval $L=U$, when both costs are constantly $L$ and the limit is $1$.
--
--   **Formalization Note** The limit has real parameter $k\in\mathbb N$, and the limiting denominator is $L>0$, so the quotient is eventually well behaved without an extra nonzero-denominator hypothesis.
-- source:
--   S. Palazzotto and A. Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission 293, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, p. 9 (printed p. 7), Remark 4.2, final displayed limit; using Jin–Lu [JL23a, Lemmas 6.1–6.2] for the input limits.

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open Filter Topology
open ProcurementPoA.DeterministicCap

theorem ProcurementPoA.DeterministicCap.Supplement.tight_ratio_limit
    (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    (opt wel : ℕ → ℝ)
    (hopt : Filter.Tendsto opt Filter.atTop (𝓝 1))
    (hwel : Filter.Tendsto wel Filter.atTop (𝓝 (1 - ProcurementPoA.DeterministicCap.epsilon))) :
    Filter.Tendsto (fun k => (U - (U - L) * wel k) / (U - (U - L) * opt k))
      Filter.atTop (𝓝 (1 + ProcurementPoA.DeterministicCap.epsilon * (U / L - 1))) := by sorry
