-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_threeColZK_no_signalling
-- name    : RelativisticZK205.ThreeCol.threeColZK_no_signalling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:10:34.624443+00:00
-- url     : https://prove2.me/theorems/18e87014-e254-4e93-b38f-b9c0bccacd35
-- title:
--   Fig. 10 — each output of 3-COLZK is uniform on $\mathbb Z_3^2$; 3-COLZK is No-Signalling
-- statement:
--   For every one of the $2^{10}$ input pairs $(z,r)$, $(z',r')$ of the 3-COLZK channel:
--
--   1. Alice's output $(\ell_0,\ell_1)$ is uniformly distributed over $\mathbb Z_3^2$;
--   2. Bob's output $(\ell'_0,\ell'_1)$ is uniformly distributed over $\mathbb Z_3^2$;
--   3. consequently 3-COLZK is No-Signalling on its entire input domain.
--
--   This is what allows simulators restricted to No-Signalling resources to use 3-COLZK, including on inputs where the condition of Fig. 10 fails.
--
--   Differences from the source:
--   - encoding: indices u, v ∈ {0, 1}, inputs (z_00, z_01, z_10, z_11, r), outputs in Z_3^2 → u, v : Bool, inputs (Bool → Bool → Bool) × Bool, outputs ZMod 3 × ZMod 3; reason: the same finite alphabets
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, Fig. 10 ("Each party's output is uniformly distributed over Z_3^2 …")

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_ThreeColZK

namespace RelativisticZK205.ThreeCol

/-- Fig. 10, p.11: on every one of its inputs, each party's output of 3-COLZK is uniform on `ℤ₃²`,
whatever the other party's input; in particular 3-COLZK is No-Signalling on its entire input
domain. -/
theorem threeColZK_no_signalling :
    (∀ a b : ColzkIn, (threeColZK a b).map Prod.fst = PMF.uniformOfFintype ColzkOut) ∧
    (∀ a b : ColzkIn, (threeColZK a b).map Prod.snd = PMF.uniformOfFintype ColzkOut) ∧
    IsNoSignalling threeColZK := by sorry

end RelativisticZK205.ThreeCol
