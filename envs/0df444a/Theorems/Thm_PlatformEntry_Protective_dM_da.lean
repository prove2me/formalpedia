-- Prove2me | Theorems.Thm_PlatformEntry_Protective_dM_da
-- name    : PlatformEntry.Protective.dM_da
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:32.56433+00:00
-- url     : https://prove2.me/theorems/e7cf45c3-6199-4a92-b485-74ce0b691cab
-- title:
--   Proof of Proposition 3, PDF p. 36 — dM(a)/da = 2c_S(Δ − a − e^B_E(a))
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$, $c_S>1/2$, $H\le 1/4$, and any $K$. Let
--   $$M(a)=\Pi^S_N(\Delta-a)-\Pi^S_E\big(e^B_E(a)\big),$$
--   where the profits (6)–(7) are evaluated at base value $a$. Then $M$ is differentiable at every real $a$ with
--   $$\frac{dM(a)}{da}=2c_S\big(\Delta-a-e^B_E(a)\big).$$
--
--   $M(a)$ compares the seller's profit when she distorts her effort down to the entry cutoff $\Delta-a$ with her profit when she accepts entry and chooses the entry first-best. Its derivative locates the upper threshold $\bar a_1$ of Proposition 3.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 3, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Proof of Proposition 3, PDF p. 36: dM(a)/da = 2c_S(Δ − a − e^B_E(a)). -/
theorem dM_da (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS)
    (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) :
    ∀ a : ℝ, HasDerivAt (fun x => Mfun δ f β cS K x)
      (2 * cS * (Delta δ f β K - a - eBE δ f β cS a)) a := by sorry

end PlatformEntry.Protective
