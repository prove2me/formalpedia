-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_disclosure_condition
-- name    : ShortTermDisclosure.Equilibrium.disclosure_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:07.662242+00:00
-- url     : https://prove2.me/theorems/ef6db3f3-c728-4221-aa40-37477b5ca91b
-- title:
--   Equation (14) at $\gamma=0$ — disclosure condition
-- statement:
--   For current value $v$, silence belief $N$, and $\lambda=\eta/(2-\eta)$, the informed manager's disclosure payoff minus silence payoff at shareholder best responses is
--
--   $$\frac{v-N}{\bar\mu}\left[\lambda(1+\lambda)\bar\mu+(1+\lambda)\left(\frac{1-\lambda}{2}v-\frac{1+\lambda}{2}N\right)\right].$$
--
--   Disclosure is optimal exactly when the product before division by $\bar\mu$ is nonnegative; in particular, it is optimal for $v\ge N$. This is equation (14) for the long-term manager. **Formalization Note** The source's strict sign is resolved to a weak sign by its explicit manager tie-break on p. 16.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), p. 36 (PDF 39), proof of Propositions 1 and 3, (14) with gamma = 0

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem disclosure_condition (P : Params) (hP : P.Standing)
    (η v N tD tN : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hv : v ∈ Set.Icc P.vlo P.vhi) (hN : N ∈ Set.Icc P.vlo P.vhi)
    (hD : IsSHBestResponse η P.muhi v tD)
    (hND : IsSHBestResponse η P.muhi N tN) :
    managerValue P.muhi tD v - managerValue P.muhi tN v =
      (v - N) / P.muhi *
        (lam η * (1 + lam η) * P.muhi +
          (1 + lam η) * ((1 - lam η) / 2 * v - (1 + lam η) / 2 * N)) ∧
    (managerValue P.muhi tN v ≤ managerValue P.muhi tD v ↔
      0 ≤ (v - N) *
        (lam η * (1 + lam η) * P.muhi +
          (1 + lam η) * ((1 - lam η) / 2 * v - (1 + lam η) / 2 * N))) ∧
    (N ≤ v → managerValue P.muhi tN v ≤ managerValue P.muhi tD v) := by sorry

end ShortTermDisclosure.Equilibrium
