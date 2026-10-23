-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_thermalEntropy_powerSeries
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.thermalEntropy_powerSeries
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:38:43.055987+00:00
-- url     : https://prove2.me/theorems/b127a416-d9e9-48eb-9c7a-f302e849060b
-- title:
--   Thermal entropy: convergent power series
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. For every real $N\ge1$, including $N=1$, the series converges and satisfies
--
--   $$g_n(N)=\ln N+1+\sum_{j=1}^{\infty}\frac{(-1)^{j+1}}{j(j+1)N^j}.$$
--
--   This expansion controls the finite-energy rate deficits. The Lean statement uses HasSum and indexes the first term by zero.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 7, Lemma 4: thermal entropy power series

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.7, Lemma 4: convergent power series in NATS, including N=1.
The natural index j starts at zero here, so the printed series index is j+1. -/
theorem thermalEntropy_powerSeries (N : ℝ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ =>
      (-1 : ℝ) ^ (j + 2) /
        (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ) * N ^ (j + 1)))
      (g N - Real.log N - 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
