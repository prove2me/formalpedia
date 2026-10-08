-- Prove2me | Theorems.Thm_StrategicQR_Game_myopic_newsvendor
-- name    : StrategicQR.Game.myopic_newsvendor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:09.13699+00:00
-- url     : https://prove2.me/theorems/92ae2808-548b-41dc-a3a6-e7377381674d
-- title:
--   Proof of Theorem 1 (ii), p. 17 — with only myopic consumers, $\pi^m$ is the newsvendor with salvage $s_l$: $F(q^m)=(p-c)/(p-v_B)$
-- statement:
--   Let $v_B<c<p$ and let $\pi^m(q)$ be the retailer's profit when all consumers are myopic ($\alpha=0$). Then:
--
--   1. for every $q>0$,
--   $$\frac{d\pi^m(q)}{dq}=p-c-pF(q)+s_lF(q);$$
--   2. $\pi^m$ has a maximizer on $[0,\infty)$;
--   3. $q\ge0$ maximizes $\pi^m$ on $[0,\infty)$ if and only if
--   $$F(q)=\frac{p-c}{p-v_B}.$$
--
--   This is the classical newsvendor with salvage value $s_l=v_B$; it is the benchmark $\pi^m$ against which Theorems 1 and 3 compare the strategic case.
--
--   **Formalization Note** With $\alpha=0$ the belief $\hat v$ has no effect; the profit is evaluated at $\hat v=\bar v$.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 17, proof of Theorem 1 (ii), unnumbered display

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- The myopic benchmark (proof of Theorem 1 (ii), p. 17). With only myopic consumers
(`α = 0`) the profit `π^m(q)` is the newsvendor profit with salvage price `s_l = vB`: for
`vB < c < p`, its derivative at `q > 0` is `p - c - pF(q) + s_l F(q)`, it has a maximizer on
`[0, ∞)`, and `q ≥ 0` is a maximizer iff `F(q) = (p - c)/(p - vB)`. -/
theorem myopic_newsvendor (M : Model) {c : ℝ} (hc : M.vB < c) (hcp : c < M.p) :
    (∀ q, 0 < q → HasDerivAt (fun q' => profit M 0 c q' M.vhi)
      (M.p - c - M.p * demandCdf M.f q + M.vB * demandCdf M.f q) q) ∧
    (∃ q ∈ Set.Ici (0 : ℝ), IsMaxOn (fun q' => profit M 0 c q' M.vhi) (Set.Ici 0) q) ∧
    (∀ q ∈ Set.Ici (0 : ℝ), (IsMaxOn (fun q' => profit M 0 c q' M.vhi) (Set.Ici 0) q ↔
      demandCdf M.f q = (M.p - c) / (M.p - M.vB))) := by sorry

end StrategicQR.Game
