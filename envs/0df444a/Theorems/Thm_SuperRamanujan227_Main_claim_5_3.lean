-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_claim_5_3
-- name    : SuperRamanujan227.Main.claim_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:52.085444+00:00
-- url     : https://prove2.me/theorems/45d9b027-bf33-44f7-8b6a-57f1d749f175
-- title:
--   Claim 5.3 — deleting the largest root does not raise the largest root of any derivative
-- statement:
--   Let $f$ be a real-rooted polynomial of degree $m\ge 2$ and let $\theta$ be its largest root. Define $g(x)=f(x)/(x-\theta)$, the polynomial obtained by deleting one occurrence of $\theta$. Then for every integer $0\le k\le m-2$,
--   $$\alpha_1\big(g^{(k)}\big)\le\alpha_1\big(f^{(k)}\big),$$
--   i.e. the largest root of $g^{(k)}$ is at most the largest root of $f^{(k)}$. Repeated roots are allowed.
--
--   It is used to pass from the reduced matching polynomial $p_M$ to the full characteristic polynomial $\chi_x(M)$ after differentiating $j$ times.
--
--   Differences from the source:
--   - encoding: g(x) = f(x)/(x − θ) → f divided by the monic polynomial x − θ (exact, θ being a root); reason: same polynomial; θ is α_1(f)
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Claim 5.3, p. 17

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
open Polynomial

namespace SuperRamanujan227.Main

/-- Claim 5.3 (p. 17): let `f` be real-rooted of degree `m ≥ 2` with largest root `θ`, and
`g = f / (x - θ)`. For every integer `0 ≤ k ≤ m - 2`, the largest root of `g^{(k)}` is at most the
largest root of `f^{(k)}`. -/
theorem claim_5_3 (f : ℝ[X]) (m : ℕ) (hf : RealRooted f) (hdeg : f.natDegree = m)
    (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ m - 2) :
    kthLargestRoot (derivative^[k] (f /ₘ (X - C (kthLargestRoot f 1)))) 1 ≤
      kthLargestRoot (derivative^[k] f) 1 := by sorry

end SuperRamanujan227.Main
