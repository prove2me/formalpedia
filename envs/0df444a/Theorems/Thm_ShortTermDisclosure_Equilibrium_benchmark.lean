-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_benchmark
-- name    : ShortTermDisclosure.Equilibrium.benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:02.828284+00:00
-- url     : https://prove2.me/theorems/e506ba6a-4b21-414d-81c4-a2f9c4a3ca3b
-- title:
--   §4.2 benchmark — full disclosure at zero short-termism
-- statement:
--   At $\eta=\lambda=0$, let $v$ be the manager's current value and $N=E[v\mid ND]$ the belief after silence. At shareholder best responses, disclosure changes the expected liquidation value by
--
--   $$E[V\mid v,\mathrm{disclose}]-E[V\mid v,ND]=\frac{(v-N)^2}{2\bar\mu}\ge0.$$
--
--   The manager therefore discloses, including at equality by the stated tie-break. **Formalization Note** The paper's comparison omits the positive factor $1/\bar\mu$; it is included here for an exact payoff identity.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), p. 16 (PDF 19), §4.2 Benchmark

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem benchmark (P : Params) (hP : P.Standing)
    (v N tD tN : ℝ) (hv : v ∈ Set.Icc P.vlo P.vhi)
    (hN : N ∈ Set.Icc P.vlo P.vhi)
    (hD : IsSHBestResponse 0 P.muhi v tD)
    (hND : IsSHBestResponse 0 P.muhi N tN) :
    managerValue P.muhi tD v - managerValue P.muhi tN v =
      (v - N) ^ 2 / (2 * P.muhi) ∧
    managerValue P.muhi tN v ≤ managerValue P.muhi tD v := by sorry

end ShortTermDisclosure.Equilibrium
